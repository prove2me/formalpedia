-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:16:17.800471+00:00
-- url     : https://prove2.me/theorems/a243abf2-9c72-498c-bd1f-53c5865af885
-- title:
--   Limits of curves on an exhaustion of the punctured plane with small $d\lambda$-energy
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level. Let $U_k\subset\mathbb{C}$ be open, increasing, with $\bigcup_k U_k=\mathbb{C}\setminus\{0\}$, and let $v_k$ be finite-energy $\tilde J$-holomorphic curves on $U_k$ with Hofer energy at most $C$, $d\lambda$-energy at most $e$, and $a(v_k(1))=0$, where $e$ is smaller than the period of every periodic Reeb orbit of period at most $C$. Then a subsequence converges in $C^\infty_{loc}(\mathbb{C}\setminus\{0\})$ to a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb{C}\setminus\{0\}$ with Hofer energy at most $C$ and $d\lambda$-energy at most $e$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of curves with small `dλ`-energy on an exhaustion of the punctured plane. Let `U_k` be
open, increasing, with `⋃ U_k = ℂ \ {0}`, and let `v_k` be finite-energy `J̃`-holomorphic curves on
`U_k` with Hofer energy at most `C`, `dλ`-energy at most `e` and `a(v_k(1)) = 0`, where `e` is smaller
than every period at most `C` of a periodic Reeb orbit. Then a subsequence converges in
`C^∞_loc(ℂ \ {0})` to a finite-energy `J̃`-holomorphic curve `w` on `ℂ \ {0}` with Hofer energy at
most `C` and `dλ`-energy at most `e`. -/
theorem exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (U : ℕ → Set ℂ) (hUo : ∀ k, IsOpen (U k))
    (hUm : Monotone U) (hUu : ⋃ k, U k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J (U k) (v k)) (C e : ℝ)
    (hE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C)
    (hd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T)
    (ha1 : ∀ k, aCoord H (v k 1) = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      energy H {z | z ≠ 0} w ≤ ENNReal.ofReal C ∧
      dlambdaEnergy H {z | z ≠ 0} w ≤ ENNReal.ofReal e ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} := by
  sorry

end FiniteEnergyPlane
