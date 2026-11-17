-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_L_3
-- name    : AggCG.Supplement.theorem_L_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:36:20.420198+00:00
-- url     : https://prove2.me/theorems/26888c6a-cb51-4d97-9f81-19a5408c1d9f
-- title:
--   Theorem L.3 — four ReLU examples give nearly linear capacity
-- statement:
--   For every $m\ge2$, there are $m$ rational four-example training sets for a one-trainable-weight ReLU, a common initialization, a positive step-size interval, and $H=O(m\log m)$ such that their normalized capped stopping-time class $1/4$-fat-shatters all $m$ sets. Hence
--
--   $$
--   \operatorname{Pdim}\ge\operatorname{fat}_{1/4}\ge m=\Omega(H/\log H).
--   $$
--
--   Every witness run is regular, and all data have bit length polynomial in $m$.
--
--   Differences from the source:
--   - encoding: regular witnesses and polynomial-bit data → the function class explicitly retains parameters regular on every constructed training set and one uniform polynomial bounds every rational example, initialization, step-size endpoint, stopping threshold, and the horizon; reason: this is the regular-parameter model fixed in §L and makes the all-data bit claim uniform
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem L.3, p.66, PDF p.67

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_AggCG_Supplement_reluCost

namespace AggCG.Supplement

/-- **Theorem L.3** (Four training examples suffice for nearly linear capacity; Sharma, *Computational
Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC
2027 submission (manuscript sha256 f7ea0248…), p.66, PDF p.67), for gradient descent with constant step
size on the one-trainable-weight ReLU loss `f_S(w) = ½ Σ_{j=1}^4 (max{0, u_j w + v_j} − y_j)²` and the
normalized capped stopping time `cost/H`. With absolute constants `C, c > 0` and one polynomial bit bound,
for every `m ≥ 2` there are `m` training sets of four rational examples, a common rational initialization
`w_0`, an interval `[η_lo, η_hi]` of positive step sizes, a threshold `ϑ > 0` and a horizon `H` with
`H ≤ C m log m` such that the class `{S_i ↦ cost_η(S_i)/H : η ∈ [η_lo, η_hi] regular}` `1/4`-fat-shatters
`S_1, …, S_m` (with regular witnesses); hence it also pseudo-shatters them, so
`Pdim ≥ fat_{1/4} ≥ m ≥ c H/log H`. All data have bit length polynomial in `m`.

**Formalization Note** A parameter is admitted in the class only if its run is regular on every training
set (it avoids the ReLU kinks through the horizon, §L, p.64). The threshold `ϑ` is part of the
construction (the proof uses `ϑ = 1/4`). -/
theorem theorem_L_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ cb e : ℕ, ∀ m : ℕ, 2 ≤ m →
      ∃ (S : Fin m → Fin 4 → ReLUEx) (w0 ηlo ηhi ϑ : ℚ) (H : ℕ),
        0 < ηlo ∧ ηlo < ηhi ∧ 0 < ϑ ∧ 2 ≤ H ∧
        (H : ℝ) ≤ C * m * Real.log m ∧ c * H / Real.log H ≤ m ∧
        BartlettNN.Margin.GammaShatters
          {g : Fin m → ℝ | ∃ η ∈ Set.Icc (ηlo : ℝ) ηhi, (∀ i, ReLURegular (S i) w0 η H) ∧
            ∀ i, g i = (reluCost (S i) w0 η ϑ H : ℝ) / H} (1 / 4) id ∧
        FoundationsML.Regression.Shatters
          {g : Fin m → ℝ | ∃ η ∈ Set.Icc (ηlo : ℝ) ηhi, (∀ i, ReLURegular (S i) w0 η H) ∧
            ∀ i, g i = (reluCost (S i) w0 η ϑ H : ℝ) / H} id ∧
        (∀ i j, (QAlgorithms.LocalHamiltonian.encRat (S i j).u).length ≤ cb * (m + 1) ^ e ∧
          (QAlgorithms.LocalHamiltonian.encRat (S i j).v).length ≤ cb * (m + 1) ^ e ∧
          (QAlgorithms.LocalHamiltonian.encRat (S i j).y).length ≤ cb * (m + 1) ^ e) ∧
        (QAlgorithms.LocalHamiltonian.encRat w0).length ≤ cb * (m + 1) ^ e ∧
        (QAlgorithms.LocalHamiltonian.encRat ηlo).length ≤ cb * (m + 1) ^ e ∧
        (QAlgorithms.LocalHamiltonian.encRat ηhi).length ≤ cb * (m + 1) ^ e ∧
        (QAlgorithms.LocalHamiltonian.encRat ϑ).length ≤ cb * (m + 1) ^ e ∧
        Nat.size H ≤ cb * (m + 1) ^ e := by sorry

end AggCG.Supplement
