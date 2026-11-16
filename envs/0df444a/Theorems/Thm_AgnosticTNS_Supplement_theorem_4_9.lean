-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_4_9
-- name    : AgnosticTNS.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:45:50.388779+00:00
-- url     : https://prove2.me/theorems/ca6b6c29-ba27-4fc9-8ebd-981dd1693910
-- title:
--   Theorem 4.9 — sequential MPS learner with $O(n^3\epsilon^{-4}(\chi d^{\kappa+1}+\log(n/\delta)))$ copies
-- statement:
--   Let $P_n$ be the path $1-2-\cdots-n$, $n\ge1$, $d\ge2$, $\chi\ge1$, and $\kappa=\max\{1,\lceil\log_d\chi\rceil\}$ (4.81). Using the sample-optimal rank-constrained tomography primitive, an unknown $|\psi\rangle\in S_d(P_n,\chi)$ can be learned to trace-norm error at most $\epsilon$ with success probability at least $1-\delta$ using
--   $$
--   O\Big(\frac{n^3}{\epsilon^4}\big(\chi d^{\kappa+1}+\log(n/\delta)\big)\Big)\quad(4.80)
--   $$
--   copies; since $d^\kappa\le d\chi$, this is at most $O\big(\frac{n^3}{\epsilon^4}(d^2\chi^2+\log(n/\delta))\big)$ (4.82). The runtime is polynomial in $n$, $d^{\kappa+1}$, $\chi$, $1/\epsilon$ and $\log(1/\delta)$.
--
--   This is the realisable MPS tomography bound used by Theorem 6.16.
--
--   **Formalization Note** One learner family on tree instances with $T$ the path graph, one absolute constant, and a polynomial-time printer from the instance padded with $n+d^{\kappa+1}+\chi+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$.
--
--   Differences from the source:
--   - generalization: classical post-processing time polynomial in n, d^{κ+1}, χ, ⌈1/ε⌉, ⌈log₂(1/δ)⌉, assuming the tomography primitive and eigendecompositions run in polynomial time → unconditional: a polynomial-time printer of the learner's circuit from the instance padded in unary with n, d^{κ+1}, χ, ⌈1/ε⌉, ⌈log₂(1/δ)⌉; reason: the paper names the primitive (Lemma 3.9, pp.38, 59), which runs in polynomial time; the unconditional statement implies the conditional one
--   - encoding: O(·) bounds → one absolute constant C > 0 chosen before every instance parameter; reason: the base mission's reading of O(·); no constant depends on n, L, d, χ, w, k, ε or δ
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: output a pure state with trace-norm error at most ε → the output decodes with the fixed decoder decodeTTN to a TTN whose normalised state is within trace norm ε of |ψ⟩⟨ψ|; reason: Gaussian-rational TTN entries cannot be exactly normalised; same guarantee
--   - encoding: the path P_n = 1 − 2 − ⋯ − n → SimpleGraph.pathGraph n on Fin n, n ≥ 1; reason: 0-based labels; the path on [n]
--   - encoding: κ = max{1, ⌈log_d χ⌉} → max 1 (Nat.clog d χ); reason: equal for d ≥ 2, χ ≥ 1
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 4.9, Eqs. (4.80)–(4.82), p.38

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_AgnosticTNS_encTreeIndex
import Definitions.Def_AgnosticTNS_Supplement_RealSuccess
import Definitions.Def_AgnosticTNS_TNSchi
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS.Supplement

/-- **Theorem 4.9 (Sample complexity of the sequential MPS learner)**, p.38 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
With the sample-optimal rank-constrained subnormalised tomography primitive of Section 2.3, an unknown
`|ψ⟩ ∈ S_d(P_n, χ)` can be learned to trace-norm error at most `ϵ` with success probability at least
`1 − δ` using `O(n³/ϵ⁴ · (χ d^{κ+1} + log(n/δ)))` copies (4.80), `κ = max{1, ⌈log_d χ⌉}` (4.81); since
`d^κ ≤ dχ` this is at most `O(n³/ϵ⁴ · (d²χ² + log(n/δ)))` (4.82). The runtime is polynomial in
`n, d^{κ+1}, χ, 1/ϵ, log(1/δ)`.

**Formalization Note** `P_n` is the path `1 − 2 − ⋯ − n` (p.66), `SimpleGraph.pathGraph n`, `n ≥ 1`. One
learner family on the tree instances `(n, P_n, d, χ, ⌈1/ϵ⌉, ⌈log₂(1/δ)⌉)`, one absolute constant, and one
polynomial-time printer of the Clifford+T circuit from the instance padded with
`n + d^{κ+1} + χ + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉`; the polynomial-time primitive assumption is discharged (Lemma
3.9). `⌈log_d χ⌉ = Nat.clog d χ`. Success is `RealSuccess` (4.1). -/
theorem theorem_4_9 :
    ∃ (Lr : CopyLearner TreeIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (ε δ : ℝ), 1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        let κ := max 1 (Nat.clog d χ)
        let i : TreeIndex := ⟨n, SimpleGraph.pathGraph n, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        g (encTreeIndex i ++ unary (n + d ^ (κ + 1) + χ + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            ((χ : ℝ) * (d : ℝ) ^ (κ + 1) + Real.log (n / δ)) ∧
          (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            ((d : ℝ) ^ 2 * (χ : ℝ) ^ 2 + Real.log (n / δ)) ∧
          ∀ ψ ∈ TNSchi d (SimpleGraph.pathGraph n) χ,
            1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε) := by sorry

end AgnosticTNS.Supplement
