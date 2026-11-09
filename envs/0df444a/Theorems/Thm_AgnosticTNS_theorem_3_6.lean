-- Prove2me | Theorems.Thm_AgnosticTNS_theorem_3_6
-- name    : AgnosticTNS.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:41:50.720655+00:00
-- url     : https://prove2.me/theorems/a79841ff-5e97-4a54-862d-4fe455373665
-- title:
--   Theorem 3.6 — agnostic tomography from a learning sequence
-- statement:
--   Let $G=([n],E)$ be a graph with bond dimension bound $\chi$ and $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ a learning sequence for $G$. Let $\rho$ be an arbitrary $n$-qudit state with
--   $$
--   \mathrm{OPT}_{G,\chi}(\rho)\ge\vartheta
--   $$
--   for a known $\vartheta\in(0,1]$. Then the agnostic sequence learner outputs a pure state $|\hat\psi\rangle$ with $\langle\hat\psi|\rho|\hat\psi\rangle\ge\mathrm{OPT}_{G,\chi}(\rho)-\epsilon$ with probability at least $1-\delta$, using
--   $$
--   O\!\left(\frac{L^5r_{\max}^2}{\vartheta\min\{\epsilon,\vartheta\}^4}\Big(d^{2a^{\mathrm{agn}}_{\max}}+\log(L/\delta)\Big)\right)
--   $$
--   copies, where $r_{\max}=\max_ir_i$ and $a^{\mathrm{agn}}_{\max}=\max_ia^{\mathrm{agn}}_i$ (Section 3.2). The classical post-processing time and the number of elementary quantum gates are polynomial in $n,L,d^{a^{\mathrm{agn}}_{\max}},\max_i\Lambda_i,1/\epsilon,1/\vartheta,\log(1/\delta)$.
--
--   The statement is one learner family for all instances and all inputs $\rho$, with one absolute constant in the copy bound.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: an algorithm using copies, with gate count and classical time bounds → one learner family: a Clifford+T circuit on $\lceil\log_2 d\rceil$-qubit encodings of the copies plus ancillas, measured at the end, whose description is printed by a polynomial-time map; reason: house model of uniform quantum algorithms; the paper's learner measures copies jointly and adaptively, which a circuit with deferred measurements realises
--   - encoding: gates and classical time polynomial in $n,L,d^{a_{\max}},\max_i\Lambda_i,1/\epsilon,1/\vartheta,\log(1/\delta)$ → a polynomial-time printer of the circuit whose input is the instance padded with $n+L+d^{a_{\max}}+\Lambda_{\max}+\lceil1/\epsilon\rceil+\lceil1/\vartheta\rceil+\lceil\log_2(1/\delta)\rceil$ ones; reason: these quantities are not input lengths; padding makes 'polynomial in them' a running-time statement
--   - encoding: real $\epsilon,\vartheta$ and $\delta$ → $\epsilon,\vartheta$ exact rationals in the instance, $\delta$ entering as $\lceil\log_2(1/\delta)\rceil$ with the guarantee stated for the real $\delta$; reason: an algorithm's inputs are finite data; rounding $\epsilon,\vartheta$ would move the step functions $p_i$ and the factor $d^{2a_{\max}}$ by more than a constant
--   - encoding: a pure state $|\hat\psi\rangle$ given by a classical description → an output string that decodes (fixed decoder `decodeTTN`) to a TTN with Gaussian-rational entries; the overlap of its normalised state is used; reason: finite-precision output (Propositions 3.8, 3.10); the decoded vector need not be a unit vector, so it is normalised
--   - reading: $O(\cdot)$ copy bound → one absolute constant $C$ chosen before every instance; reason: the paper's constant in (3.54) is absolute
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 3.6, Eqs. (3.52)–(3.54), p.23

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

/-- **Theorem 3.6 (Agnostic tomography from a learning sequence)**, p.23 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `G = ([n], E)`
have bond bound `χ`, `L = (S_i, I_i, F_i)_{i=1}^L` a learning sequence for `G`, and `ρ` an arbitrary
`n`-qudit state with `OPT_{G,χ}(ρ) ≥ ϑ` (3.52) for a known `ϑ ∈ (0, 1]`. Then Algorithm 1 outputs a
pure state `|ψ̂⟩` with `⟨ψ̂|ρ|ψ̂⟩ ≥ OPT_{G,χ}(ρ) − ϵ` (3.53) with probability at least `1 − δ`, using
`O(L⁵ r_max² / (ϑ min{ϵ, ϑ}⁴) · (d^{2a^agn_max} + log(L/δ)))` copies (3.54). The classical
post-processing time and the number of elementary quantum gates are polynomial in
`n, L, d^{a^agn_max}, max_i Λ_i, 1/ϵ, 1/ϑ, log(1/δ)`.

**Formalization Note** One learner family over the instances `(n, G, L, d, χ, ϵ, ϑ, ⌈log₂(1/δ)⌉)`
(`ϵ, ϑ` exact rationals), one absolute constant `C`, and one polynomial-time printer of the circuit
whose input is the instance padded with `n + L + d^{a_max} + Λ_max + ⌈1/ϵ⌉ + ⌈1/ϑ⌉ + ⌈log₂(1/δ)⌉` ones.
The output decodes (fixed decoder `decodeTTN`) to a TTN with Gaussian-rational entries whose
normalised state has the overlap. `r_max = max_i r_i`, `a_max = max_i a^agn_i`, `Λ_max = max_i Λ_i`. -/
theorem theorem_3_6 :
    ∃ (Lr : CopyLearner SeqIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (Ls : LearningSequence n) (ε ϑ : ℚ) (δ : ℝ),
        1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < ϑ → ϑ ≤ 1 → 0 < δ → δ < 1 →
        g (encSeqIndex ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ++
            unary (n + Ls.L + d ^ Finset.univ.sup (aAgn d G χ Ls ε ϑ) +
              Finset.univ.sup (LambdaP G χ Ls ε ϑ) + ⌈1 / (ε : ℝ)⌉₊ + ⌈1 / (ϑ : ℝ)⌉₊ +
              ⌈Real.logb 2 (1 / δ)⌉₊)) =
            Lr.code ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ∧
          (Lr.copies ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ : ℝ) ≤
            C * ((Ls.L : ℝ) ^ 5 * ((Finset.univ.sup (rr G χ Ls) : ℕ) : ℝ) ^ 2 /
                ((ϑ : ℝ) * (min (ε : ℝ) ϑ) ^ 4)) *
              ((d : ℝ) ^ (2 * Finset.univ.sup (aAgn d G χ Ls ε ϑ)) + Real.log (Ls.L / δ)) ∧
          ∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            (ϑ : ℝ) ≤ OPT d G χ ρ →
            1 - δ ≤ Lr.prob ⟨n, G, Ls, d, χ, ε, ϑ, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ρ
              (fun s => ∃ (m : ℕ) (D : TTN m n d), decodeTTN n d s = some ⟨m, D⟩ ∧
                D.state ≠ 0 ∧ OPT d G χ ρ - ε ≤ expVal ρ D.state / ∑ x, ‖D.state x‖ ^ 2) := by sorry

end AgnosticTNS
