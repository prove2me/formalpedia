-- Prove2me | Theorems.Thm_AgnosticTNS_corollary_5_2
-- name    : AgnosticTNS.corollary_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:40:44.86986+00:00
-- url     : https://prove2.me/theorems/43e5a0a7-3e76-40f9-9ba9-c3212196164b
-- title:
--   Corollary 5.2 — TTN tomography without an overlap promise
-- statement:
--   Let $T$ be a tree on $n\ge2$ vertices and $b$ the maximum number of children after rooting $T$ at a leaf. For an arbitrary state $\rho$ on $(\mathbb C^d)^{\otimes n}$, one can output a pure state whose overlap with $\rho$ is at least $\mathrm{OPT}_{T,\chi}(\rho)-\epsilon$ with probability at least $1-\delta$. For fixed $b$, the number of copies is
--   $$
--   \widetilde O\!\left(\frac{d^{2+2b}\,n^{5+4b}\,\chi^{2+2b}}{\epsilon^{5+4b}}\right),
--   $$
--   and the running time is polynomial in $n,d,\chi,1/\epsilon,\log(1/\delta)$. The output is a TTN on $T$ with bond dimension $O(dn^2\chi/\epsilon^2)$.
--
--   This is the formal version of Theorem 1.1: efficient agnostic learning of tree tensor network states of bounded branching, for arbitrary mixed inputs and with no promise on the optimal overlap.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: an algorithm using copies, with gate count and classical time bounds → one learner family: a Clifford+T circuit on $\lceil\log_2 d\rceil$-qubit encodings of the copies plus ancillas, measured at the end, whose description is printed by a polynomial-time map; reason: house model of uniform quantum algorithms; the paper's learner measures copies jointly and adaptively, which a circuit with deferred measurements realises
--   - encoding: a pure state $|\hat\psi\rangle$ given by a classical description → an output string that decodes (fixed decoder `decodeTTN`) to a TTN with Gaussian-rational entries; the overlap of its normalised state is used; reason: finite-precision output (Propositions 3.8, 3.10); the decoded vector need not be a unit vector, so it is normalised
--   - reading: $\widetilde O(d^{2+2b}n^{5+4b}\chi^{2+2b}/\epsilon^{5+4b})$ copies for fixed $b$ → copies at most $C_b\big(d^{2+2b}n^{5+4b}\chi^{2+2b}/\epsilon^{5+4b}+n^5\chi^2\epsilon^{-5}\log(n/\delta)\big)$ with $C_b$ depending only on $b$; reason: the bound obtained by substituting (5.7) into (5.2) at $\vartheta=\epsilon$; the $\widetilde O$ hides the $\log(n/\delta)$ term (p.3: "$\widetilde O$ suppresses logarithmic factors, including the dependence on $1/\delta$"), and this explicit form is stronger than any polylogarithmic reading
--   - reading: $b$, "the maximum number of children after rooting $T$ at a leaf" → all trees with `leafBranching T` $\le b$ (some leaf of branching at most $b$); reason: the page does not name the leaf; this is the larger class of trees for each $b$
--   - reading: "For an arbitrary state $\rho$, one can output" → one learner family for all instances and all $\rho$; reason: a learner chosen after $\rho$ could output the optimum; the paper's algorithm does not depend on $\rho$
--   - encoding: real $\epsilon,\delta$; running time polynomial in $n,d,\chi,1/\epsilon,\log(1/\delta)$ → the instance carries $\lceil1/\epsilon\rceil$ and $\lceil\log_2(1/\delta)\rceil$ in unary with $n,d,\chi$ and the adjacency matrix of $T$; for each $b$ a polynomial-time printer of the circuit from it; guarantees stated for the real $\epsilon,\delta$; reason: an algorithm's inputs are finite data; rounding changes the bounds by factors depending only on $b$
--   - encoding: bond dimension $O(dn^2\chi/\epsilon^2)$ → every bond at most $C\,dn^2\chi/\epsilon^2$ with one absolute constant $C$ chosen before $b$; reason: the paper's constant (2048 in (5.7)) is absolute
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.2, Eq. (5.6), p.40 (formal version of Theorem 1.1, p.3)

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_AgnosticTNS_encTreeIndex
import Definitions.Def_AgnosticTNS_decodeTTN
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_AgnosticTNS_TTN_IsOn
import Definitions.Def_AgnosticTNS_OPT
import Definitions.Def_AgnosticTNS_leafBranching
import Definitions.Def_WildeQIT_IsDensityOperator
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **Corollary 5.2 (TTN tomography without an overlap promise)**, p.40 (formal version of
Theorem 1.1, p.3) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `T` be a tree on `n ≥ 2` vertices and `b` the maximum number of children
after rooting `T` at a leaf. For an arbitrary state `ρ`, one can output a pure state whose overlap with
`ρ` is at least `OPT_{T,χ}(ρ) − ϵ` with probability at least `1 − δ`. For fixed `b`, the number of copies
is `Õ(d^{2+2b} n^{5+4b} χ^{2+2b} / ϵ^{5+4b})` (5.6), and the running time is polynomial in
`n, d, χ, 1/ϵ, log(1/δ)`. The output is a TTN on `T` with bond dimension `O(d n² χ / ϵ²)`.

**Formalization Note** One learner family `Lr` for all instances and all `ρ` (no promise on `OPT`, mixed
`ρ`), indexed by `(n, T, d, χ, ⌈1/ϵ⌉, ⌈log₂(1/δ)⌉)`; per `b` one constant `C` and one polynomial-time
printer of the circuit from the unary instance, valid on all trees with `leafBranching T ≤ b`. The `Õ`
is the explicit bound `C (d^{2+2b} n^{5+4b} χ^{2+2b}/ϵ^{5+4b} + n⁵χ²/ϵ⁵ · log(n/δ))` obtained by
substituting (5.7) into (5.2). The output decodes (fixed decoder `decodeTTN`) to a Gaussian-rational TTN
on `T` with every bond at most `C_b d n² χ / ϵ²` (one absolute constant `C_b`, chosen before `b`) whose normalised state has overlap at least
`OPT_{T,χ}(ρ) − ϵ`. The learner is a Clifford+T circuit on `⌈log₂ d⌉`-qubit encodings of the copies
plus ancillas, measured at the end. -/
theorem corollary_5_2 :
    ∃ (Lr : CopyLearner TreeIndex (fun i => i.n) (fun i => i.d)) (Cb : ℝ), 0 < Cb ∧
      ∀ b : ℕ, ∃ (C : ℝ) (g : Str → Str), 0 < C ∧ PolyTimeComputable g ∧
        ∀ (n d χ : ℕ) (T : SimpleGraph (Fin n)) (ε δ : ℝ),
          2 ≤ n → T.IsTree → leafBranching T ≤ b → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
          g (encTreeIndex ⟨n, T, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩) =
              Lr.code ⟨n, T, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ∧
            (Lr.copies ⟨n, T, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩ : ℝ) ≤
              C * ((d : ℝ) ^ (2 + 2 * b) * (n : ℝ) ^ (5 + 4 * b) * (χ : ℝ) ^ (2 + 2 * b) /
                  ε ^ (5 + 4 * b) + (n : ℝ) ^ 5 * (χ : ℝ) ^ 2 / ε ^ 5 * Real.log (n / δ)) ∧
            ∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
              1 - δ ≤ Lr.prob ⟨n, T, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩ ρ
                (fun s => ∃ D : TTN n n d, decodeTTN n d s = some ⟨n, D⟩ ∧ D.IsOn T ∧
                (∀ v, D.parent v ≠ none → (D.bond v : ℝ) ≤ Cb * d * (n : ℝ) ^ 2 * χ / ε ^ 2) ∧ D.state ≠ 0 ∧
                OPT d T χ ρ - ε ≤ expVal ρ D.state / ∑ x, ‖D.state x‖ ^ 2) := by sorry

end AgnosticTNS
