-- Prove2me | Theorems.Thm_AgnosticTNS_corollary_3_7
-- name    : AgnosticTNS.corollary_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:43:46.130985+00:00
-- url     : https://prove2.me/theorems/6a90d0fa-22dd-460e-9a23-cd54fad6a688
-- title:
--   Corollary 3.7 — agnostic tomography without an overlap promise
-- statement:
--   Let $G=([n],E)$ be a graph with bond dimension bound $\chi$ and $\mathcal L$ a learning sequence for $G$. For every $n$-qudit state $\rho$, the learner outputs a pure state $|\hat\psi\rangle$ with
--   $$
--   \langle\hat\psi|\rho|\hat\psi\rangle\ge\mathrm{OPT}_{G,\chi}(\rho)-\epsilon
--   $$
--   with probability at least $1-\delta$, using
--   $$
--   O\!\left(\frac{L^5r_{\max}^2}{\epsilon^5}\Big(d^{2a^{\mathrm{agn}}_{\max}}+\log(L/\delta)\Big)\right)
--   $$
--   copies, where $p_i$ and $a^{\mathrm{agn}}_{\max}$ are evaluated at $\vartheta=\epsilon$. Both the number of elementary quantum gates and the classical post-processing time are polynomial in $n,L,d^{a^{\mathrm{agn}}_{\max}},\max_i\Lambda_i,1/\epsilon,\log(1/\delta)$.
--
--   No lower bound on $\mathrm{OPT}_{G,\chi}(\rho)$ is assumed.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: an algorithm using copies, with gate count and classical time bounds → one learner family: a Clifford+T circuit on $\lceil\log_2 d\rceil$-qubit encodings of the copies plus ancillas, measured at the end, whose description is printed by a polynomial-time map; reason: house model of uniform quantum algorithms; the paper's learner measures copies jointly and adaptively, which a circuit with deferred measurements realises
--   - encoding: gates and classical time polynomial in $n,L,d^{a_{\max}},\max_i\Lambda_i,1/\epsilon,\log(1/\delta)$ → a polynomial-time printer of the circuit whose input is the instance padded with $n+L+d^{a_{\max}}+\Lambda_{\max}+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$ ones; reason: these quantities are not input lengths; padding makes 'polynomial in them' a running-time statement
--   - encoding: real $\epsilon,\vartheta$ and $\delta$ → $\epsilon,\vartheta$ exact rationals in the instance, $\delta$ entering as $\lceil\log_2(1/\delta)\rceil$ with the guarantee stated for the real $\delta$; reason: an algorithm's inputs are finite data; rounding $\epsilon,\vartheta$ would move the step functions $p_i$ and the factor $d^{2a_{\max}}$ by more than a constant
--   - encoding: a pure state $|\hat\psi\rangle$ given by a classical description → an output string that decodes (fixed decoder `decodeTTN`) to a TTN with Gaussian-rational entries; the overlap of its normalised state is used; reason: finite-precision output (Propositions 3.8, 3.10); the decoded vector need not be a unit vector, so it is normalised
--   - reading: $O(\cdot)$ copy bound → one absolute constant $C$ chosen before every instance; reason: the paper's constant in (3.54) is absolute
--   - reading: "For every $n$-qudit state $\rho$, there is an algorithm" → one learner for all $\rho$; reason: a learner chosen after $\rho$ could output the optimum; the paper's algorithm (Algorithm 1 with $\vartheta=\epsilon$) does not depend on $\rho$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 3.7, Eqs. (3.57)–(3.58), p.24

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_AgnosticTNS_encSeqIndex
import Definitions.Def_AgnosticTNS_decodeTTN
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_AgnosticTNS_OPT
import Definitions.Def_AgnosticTNS_aAgn
import Definitions.Def_AgnosticTNS_LambdaP
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **Corollary 3.7 (Agnostic tomography without an overlap promise)**, p.24 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `G = ([n], E)`
have bond bound `χ` and `L` be a learning sequence for `G`. For every `n`-qudit state `ρ` there is an
algorithm that outputs a pure state `|ψ̂⟩` with `⟨ψ̂|ρ|ψ̂⟩ ≥ OPT_{G,χ}(ρ) − ϵ` (3.57) with probability at
least `1 − δ`, using `O(L⁵ r_max²/ϵ⁵ · (d^{2a^agn_max} + log(L/δ)))` copies (3.58), with `p_i` and
`a^agn_max` evaluated at `ϑ = ϵ`. The number of gates and the classical post-processing time are
polynomial in `n, L, d^{a^agn_max}, max_i Λ_i, 1/ϵ, log(1/δ)`.

**Formalization Note** One learner family for all `ρ` (the algorithm does not depend on `ρ`), on the
instances of `theorem_3_6` with `ϑ = ϵ`; padding `n + L + d^{a_max} + Λ_max + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉`. -/
theorem corollary_3_7 :
    ∃ (Lr : CopyLearner SeqIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (Ls : LearningSequence n) (ε : ℚ) (δ : ℝ),
        1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        g (encSeqIndex ⟨n, G, Ls, d, χ, ε, ε, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ++
            unary (n + Ls.L + d ^ Finset.univ.sup (aAgn d G χ Ls ε ε) +
              Finset.univ.sup (LambdaP G χ Ls ε ε) + ⌈1 / (ε : ℝ)⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) =
            Lr.code ⟨n, G, Ls, d, χ, ε, ε, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ∧
          (Lr.copies ⟨n, G, Ls, d, χ, ε, ε, ⌈Real.logb 2 (1 / δ)⌉₊⟩ : ℝ) ≤
            C * ((Ls.L : ℝ) ^ 5 * ((Finset.univ.sup (rr G χ Ls) : ℕ) : ℝ) ^ 2 / (ε : ℝ) ^ 5) *
              ((d : ℝ) ^ (2 * Finset.univ.sup (aAgn d G χ Ls ε ε)) + Real.log (Ls.L / δ)) ∧
          ∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            1 - δ ≤ Lr.prob ⟨n, G, Ls, d, χ, ε, ε, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ρ
              (fun s => ∃ (m : ℕ) (D : TTN m n d), decodeTTN n d s = some ⟨m, D⟩ ∧
                D.state ≠ 0 ∧ OPT d G χ ρ - ε ≤ expVal ρ D.state / ∑ x, ‖D.state x‖ ^ 2) := by sorry

end AgnosticTNS
