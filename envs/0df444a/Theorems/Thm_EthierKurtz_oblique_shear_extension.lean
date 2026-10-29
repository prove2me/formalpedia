-- Prove2me | Theorems.Thm_EthierKurtz_oblique_shear_extension
-- name    : EthierKurtz.oblique_shear_extension
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:44:35.143995+00:00
-- url     : https://prove2.me/theorems/4e7d8beb-41a8-4331-be16-a72796694524
-- title:
--   Shear extension of a $C^{2,\mu}$ graph function
-- statement:
--   From the extension package of the statement: for a $C^{2,\mu}$ boundary graph function $\psi$ and a $C^{1,\mu}$ field there is a shear map $$\Phi(z)=z+G(z)\,w$$ with $G$ of class $C^{2,\mu}$ and the derivative identities and bounds of the statement.
--
--   Role: first half of the chart construction.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.2 and Lemma 6.37-6.38 (extension); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_shear_extension (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hP : ∀ (M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (e : EuclideanSpace ℝ (Fin (n + 1))),
        (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
        (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
        ∃ (E : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (DE : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (D2E : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)),
          (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
          (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
          (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
          ∃ C, 0 ≤ C ∧ ∀ x x' : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
            ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ) :
    ∀ {m : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin (n + 1))) (e : EuclideanSpace ℝ (Fin (n + 1))) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i),
    ∃ (Gm : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (DG : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) (D2G : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 ≤ r → ∃ K, let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ inner ℝ x e ∧ dist x c ≤ r}
        0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Gm x - Gm y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DG x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖DG x - DG y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2G x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖D2G x - D2G y‖ ≤ K * ‖x - y‖ ^ μ)) := by sorry

end EthierKurtz
