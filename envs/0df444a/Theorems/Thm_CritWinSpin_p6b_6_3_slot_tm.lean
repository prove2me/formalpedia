-- Prove2me | Theorems.Thm_CritWinSpin_p6b_6_3_slot_tm
-- name    : CritWinSpin.p6b_6_3_slot_tm
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:36.070534+00:00
-- url     : https://prove2.me/theorems/cc532f9b-f486-4385-957a-cfe010b3f987
-- title:
--   Quantized cloud dynamic programming and rejection sampling as one PPT slot machine
-- statement:
--   For every single-site GHS law $\rho$ of type $p$ and every admissible choice of the gadget parameters, there is one probabilistic polynomial-time algorithm implementing one slot of $\hat L_{T,k}$. On input $(J_0,h_0,\hat u,y)$ it performs the two steps on p.24: first sample the clouds independently by dynamic programming on their sums, approximating the exponential weights to polynomially many bits, and then accept with a quantized uniform threshold according to $a_y(\sigma)=e^{D_y(\sigma)-1}\mathbf1_{G_y}(\sigma)$.
--
--   Its output law is a probability distribution on $A^N\cup\{\bot\}$. There are a quantized proposal law $\tilde\nu_y$ and acceptance function $\tilde a_y$ such that the probability of outputting $\sigma$ is exactly $\tilde\nu_y(\sigma)\tilde a_y(\sigma)$, every positive-probability output lies in the support of the ideal rejection step, and
--   $$
--   \sum_\sigma|\tilde\nu_y(\sigma)-\nu_y(\sigma)|
--    \le \tfrac12e^{-2n^2},
--   $$
--   $$
--   0<\tilde\nu_y(\sigma)\ \Longrightarrow\
--    |\tilde a_y(\sigma)-a_y(\sigma)|\le\tfrac12e^{-2n^2}.
--   $$
--   The two factors together account for the total variation error $e^{-2n^2}$ stipulated for step 1 of the procedure, while support containment preserves exact sign decoding.
--
--   **Formalization Note.** `slotM` is uniform in the input length and has no advice; it handles arbitrary rational $\hat u$ satisfying (28). Its unknown output string decodes to $\bot$ through `decCloud`. This lemma supplies only the implementation and its two basic approximation bounds; conversion to total variation distance and `LhatDecodes` is already handled by `CritWinSpin.p6b_6_3_math_approx`.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), §6.2, p.24, procedure $\hat L_{T,k}$, steps 1–2, exact subset-sum dynamic programming and quantized rejection sampling; Theorem 6.3(ii), pp.24–25.

import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
set_option autoImplicit false

/-- The quantized subset-sum dynamic program for the independent clouds, followed by the
uniform-threshold rejection step. -/
theorem CritWinSpin.p6b_6_3_slot_tm (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
      ∃ slotM : PPT,
        ∀ (n : ℕ) (H : Inst n), H.1.IsSymm → (∀ i, H.1 i i = 0) →
          width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
          ∀ (û : ℚ), IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
            ∀ y : BinCfg n,
              IsDistribution (slotKernel S p Cc slotM H û y) ∧
              ∃ (nuT aT : Config S (Fin n × Fin (cloudSize p Cc n)) → ℝ),
                (∀ σ, 0 ≤ nuT σ) ∧ ∑ σ, nuT σ = 1 ∧ (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) ∧
                (∀ σ, slotKernel S p Cc slotM H û y (some σ) = nuT σ * aT σ) ∧
                (∀ σ, 0 < slotKernel S p Cc slotM H û y (some σ) →
                  0 < idealSlot S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ))
                    (castM H.1) (castV H.2) (û : ℝ) y (some σ)) ∧
                ∑ σ : Config S (Fin n × Fin (cloudSize p Cc n)),
                  |nuT σ - nuProd S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ)) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2)) ∧
                (∀ σ, 0 < nuT σ →
                  |aT σ - ay (castM H.1) (castV H.2) (û : ℝ) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2))) := by sorry
