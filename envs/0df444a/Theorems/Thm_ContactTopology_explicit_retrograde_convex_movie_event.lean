-- Prove2me | Theorems.Thm_ContactTopology_explicit_retrograde_convex_movie_event
-- name    : ContactTopology.explicit_retrograde_convex_movie_event
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T06:28:04.552384+00:00
-- url     : https://prove2.me/theorems/195151c3-5f16-4b42-abba-7f52fc5c6a14
-- title:
--   An explicit retrograde saddle connection and three-arc dividing switch
-- statement:
--   Consider standard contact three-space $(\mathbb R^3,\ker(dZ-P\,dQ))$ and the smooth family of surfaces
--   $$S_t(x,y)=(x,xy-t,xt+(1-x^2)y).$$
--   Every $S_t$ is an embedding with injective differential, and its pulled-back contact form and characteristic vector field are
--   $$\beta_t=(2t-3xy)\,dx+(1-x^2)\,dy,\qquad X_t=(1-x^2,3xy-2t).$$
--
--   The contact field $E=(0,P,Z)$ has the complete flow $\Phi_s=(Q,e^sP,e^sZ)$, satisfying $\Phi_s^*\alpha=e^s\alpha$. It is transverse to every $S_t$ with $t\ne0$. At $t=0$, every smooth contact field defined on any open neighborhood of the segment $S_0([-1,1]\times\{0\})$ is tangent to the surface somewhere on the open segment. Thus this slice has an actual local obstruction to convexity.
--
--   The two characteristic singularities of $S_t$ are $(-1,-2t/3)$ and $(1,2t/3)$. At zero their linearizations are $\operatorname{diag}(2,-3)$ and $\operatorname{diag}(-2,3)$, respectively. The characteristic segment $y=0$, $-1<x<1$, is oriented from the negative saddle to the positive saddle.
--
--   For every $0<t<1$, set $a=(\sqrt{t^2+4}-t)/2$ and $b=(\sqrt{t^2+4}+t)/2$, so $0<a<1<b<2$. In the rectangle $B=[-2,2]\times[-1,1]$, the entire dividing set of $S_t$ for the actual field $E$ consists of exactly three pairwise disjoint smooth regular embedded arcs. Their parameter-plane endpoint pairs are
--
--   | Slice | Left arc | Middle arc | Right arc |
--   |---|---|---|---|
--   | $S_t$ | $(-2,-2t/3)$ to $(-b,-1)$ | $(-a,1)$ to $(a,-1)$ | $(b,1)$ to $(2,2t/3)$ |
--   | $S_{-t}$ | $(-2,2t/3)$ to $(-b,1)$ | $(-a,-1)$ to $(a,1)$ | $(b,-1)$ to $(2,-2t/3)$ |
--
--   Each physical arc meets the physical rectangle boundary only at its two endpoints. The negative-parameter arcs are obtained by the explicit ambient reflection $(Q,P,Z)\mapsto(Q,-P,-Z)$.
--
--   This is an explicit local event with a three-arc dividing reconnection. It does not assert generic realization in an arbitrary family, uniqueness of the local model, Legendrian rectangle boundary, an attached bypass disk, or Legendrian core classification.
-- source:
--   Original explicit polynomial realization of a retrograde saddle connection and its three-arc dividing switch in standard contact space. Context and event description: Ko Honda, Gluing tight contact structures, https://arxiv.org/pdf/math/0102029, Section 2.2.3, Lemma 2.10 proof, printed pp. 17-18 (published Duke Mathematical Journal 115(3), 435-478, 2002, Section 3.2.3, Lemma 3.10). Also Hyunki Min, https://arxiv.org/html/2207.03590v2, Theorem 2.5 and Theorem 2.6. The coordinate formulas and their proofs are supplied here as a separate auxiliary construction; this is not a genericity theorem, a local-normal-form uniqueness theorem, or a proof of bypass attachment.

import Definitions.Def_ContactTopology_RetrogradeMovie
import Mathlib.Topology.Separation.Hausdorff
open BirkhoffGlobalSection ContactTopology.TwoArcDisk ContactTopology.RetrogradeMovie Set Function Topology
open scoped ContDiff

theorem ContactTopology.explicit_retrograde_convex_movie_event :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => model p.1 p.2) ∧
    (∀ t : ℝ, IsEmbedding (model t) ∧ ∀ u : Plane, Injective (fderiv ℝ (model t) u)) ∧
    (∀ t : ℝ, ∀ u v : Plane, jetForm (model t u) (fderiv ℝ (model t) u v)=
      (2*t-3*u 0*u 1)*v 0+(1-u 0^2)*v 1) ∧
    ContDiff ℝ ∞ euler ∧
    (∀ p v : Space, -(euler p 1)*v 0+jetForm p (fderiv ℝ euler p v)=jetForm p v) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => flow z.1 z.2) ∧
    (∀ p : Space, flow 0 p=p) ∧
    (∀ s r : ℝ, ∀ p : Space, flow (s+r) p=flow s (flow r p)) ∧
    (∀ s : ℝ, ∀ p : Space, flow (-s) (flow s p)=p) ∧
    (∀ s : ℝ, ∀ p v : Space,
      jetForm (flow s p) (fderiv ℝ (flow s) p v)=Real.exp s*jetForm p v) ∧
    (∀ s : ℝ, ∀ p : Space, HasDerivAt (fun r => flow r p) (euler (flow s p)) s) ∧
    (∀ t : ℝ, t≠0 → ∀ u v : Plane, euler (model t u)≠fderiv ℝ (model t) u v) ∧
    (∀ (Y : Space → Space) (O : Set Space), IsOpen O →
      (∀ x ∈ Icc (-1:ℝ) 1, model 0 ![x,0] ∈ O) → ContDiffOn ℝ ∞ Y O →
      (∀ p ∈ O, ∃ a : ℝ, ∀ v : Space,
        -(Y p 1)*v 0+jetForm p (fderiv ℝ Y p v)=a*jetForm p v) →
      ∃ x ∈ Ioo (-1:ℝ) 1, ∃ v : Plane,
        Y (model 0 ![x,0])=fderiv ℝ (model 0) ![x,0] v) ∧
    (∀ t : ℝ, ∀ u : Plane, characteristic t u=0 ↔
      u= ![-1,-2*t/3] ∨ u= ![1,2*t/3]) ∧
    (∀ v : Plane, fderiv ℝ (characteristic 0) ![-1,0] v=![2*v 0,-3*v 1] ∧
      fderiv ℝ (characteristic 0) ![1,0] v= ![-2*v 0,3*v 1]) ∧
    (∀ x : ℝ, HasDerivAt connection ![1,0] x ∧
      characteristic 0 (connection x)=(1-x^2) • deriv connection x) ∧
    (∀ x ∈ Ioo (-1:ℝ) 1, 0 < 1-x^2) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      (0 < inner t ∧ inner t < 1 ∧ 1 < outer t ∧ outer t < 2 ∧
        inner t^2+t*inner t=1 ∧ outer t^2-t*outer t=1) ∧
      physicalZero t=range (physicalArc t 0) ∪ range (physicalArc t 1) ∪ range (physicalArc t 2) ∧
      physicalZero (-t)=range (reflect ∘ physicalArc t 0) ∪
        range (reflect ∘ physicalArc t 1) ∪ range (reflect ∘ physicalArc t 2) ∧
      (∀ j : Fin 3, (bounds t j).1 < (bounds t j).2 ∧
        IsEmbedding (physicalArc t j) ∧ IsEmbedding (reflect ∘ physicalArc t j) ∧
        (∀ x ∈ interval t j,
          (ContDiffAt ℝ ∞ (model t ∘ graph t) x ∧ deriv (model t ∘ graph t) x≠0) ∧
          (ContDiffAt ℝ ∞ (reflect ∘ model t ∘ graph t) x ∧
            deriv (reflect ∘ model t ∘ graph t) x≠0)) ∧
        ∀ x : Icc (bounds t j).1 (bounds t j).2,
          (physicalArc t j x ∈ model t '' boxBoundary ↔
            x.val=(bounds t j).1 ∨ x.val=(bounds t j).2) ∧
          ((reflect ∘ physicalArc t j) x ∈ model (-t) '' boxBoundary ↔
            x.val=(bounds t j).1 ∨ x.val=(bounds t j).2) ∧
          ((x.val=(bounds t j).1 → physicalArc t j x=model t (leftEnd t j)) ∧
            (x.val=(bounds t j).2 → physicalArc t j x=model t (rightEnd t j))) ∧
          ((x.val=(bounds t j).1 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (leftEnd t j))) ∧
            (x.val=(bounds t j).2 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (rightEnd t j))))) ∧
      ∀ i j : Fin 3, i≠j →
        Disjoint (range (physicalArc t i)) (range (physicalArc t j)) ∧
        Disjoint (range (reflect ∘ physicalArc t i)) (range (reflect ∘ physicalArc t j)) := by sorry
