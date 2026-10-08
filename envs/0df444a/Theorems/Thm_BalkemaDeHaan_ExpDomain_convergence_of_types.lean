-- Prove2me | Theorems.Thm_BalkemaDeHaan_ExpDomain_convergence_of_types
-- name    : BalkemaDeHaan.ExpDomain.convergence_of_types
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:28.376198+00:00
-- url     : https://prove2.me/theorems/3c1a9b5f-8ab2-4d73-b66a-ea46216bb169
-- title:
--   Remark after Lemma 1 — convergence of types for scaled tails
-- statement:
--   Let $R$ be the survival function of a probability law. Suppose $c_nR(b_n+xa_n)$ and $c_nR(b_n^*+xa_n^*)$ converge weakly on $(x_0,\infty)$ to tails $S(x)$ and $S^*(x)$, with $c_n,a_n,a_n^*>0$. If both limit tails are strictly positive there and tend to zero at infinity, then there are constants $A>0$ and $B$ such that
--
--   $$\frac{a_n^*}{a_n}\to A,\qquad \frac{b_n^*-b_n}{a_n}\to B,\qquad S^*(x)=S(B+xA).$$
--
--   This identifies how two normalizations of the same tail must be related. The paper invokes the remark again while extending equation (11) from a half-line to all real arguments.
--
--   **Formalization Note** Weak convergence here means convergence at continuity points of each limit. The tails are explicitly antitone and right-continuous on $(x_0,\infty)$, properties used in the remark's comparison argument. The identity is stated where both $x$ and $B+xA$ lie in that interval, so both values are determined by the hypotheses.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 795 (PDF 4), Remark after Corollary to Lemma 1

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory

/-- Remark after the Corollary to Lemma 1, p. 795. -/
theorem convergence_of_types (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c a aStar b bStar : ℕ → ℝ) (S SStar : ℝ → ℝ) (x₀ : ℝ)
    (hc : ∀ n, 0 < c n) (ha : ∀ n, 0 < a n) (haStar : ∀ n, 0 < aStar n)
    (hS_mono : AntitoneOn S (Set.Ioi x₀))
    (hSStar_mono : AntitoneOn SStar (Set.Ioi x₀))
    (hS_right : ∀ x > x₀, ContinuousWithinAt S (Set.Ici x) x)
    (hSStar_right : ∀ x > x₀, ContinuousWithinAt SStar (Set.Ici x) x)
    (hS_pos : ∀ x > x₀, 0 < S x) (hSStar_pos : ∀ x > x₀, 0 < SStar x)
    (hS_zero : Tendsto S atTop (nhds 0))
    (hSStar_zero : Tendsto SStar atTop (nhds 0))
    (hS : ∀ x > x₀, ContinuousAt S x →
      Tendsto (fun n => c n * BalkemaDeHaan.LimitTypes.tail μ (b n + x * a n)) atTop (nhds (S x)))
    (hSStar : ∀ x > x₀, ContinuousAt SStar x →
      Tendsto (fun n => c n * BalkemaDeHaan.LimitTypes.tail μ (bStar n + x * aStar n)) atTop (nhds (SStar x))) :
    ∃ A B : ℝ, 0 < A ∧
      Tendsto (fun n => aStar n / a n) atTop (nhds A) ∧
      Tendsto (fun n => (bStar n - b n) / a n) atTop (nhds B) ∧
      ∀ x : ℝ, x₀ < x → x₀ < B + x * A → SStar x = S (B + x * A) := by sorry

end BalkemaDeHaan.ExpDomain
