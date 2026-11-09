-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_theorem_2_6
-- name    : BourgainUnion.Euclidean.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:44.374249+00:00
-- url     : https://prove2.me/theorems/35dfbb58-40b2-4bb4-803e-f4775cecc14c
-- title:
--   Theorem 2.6 — the specific Voronoi-cell map
-- statement:
--   Let $\psi$ be any hyperplane-collapse map with positive constants $a,b$ from Corollary 2.2. Let $V_1,\ldots,V_r$ be nonempty subsets of a metric space $X$, with $r\ge1$; they need not cover $X$. Suppose $\phi_i$ is a $D$-terminal embedding of $V_i$, where $D\ge1$, and let $f$ be the fixed direct-sum map of Section 2.3. Put
--   $$C=\max\{1,2\sqrt2\,b\},\qquad c=\min\{1,a/2\}.$$
--   Then $f$ is $C$-Lipschitz and for every $x\in N_i$ and $y\in X$,
--   $$\|f(x)-f(y)\|\ge c\left(\min\{d(x,y)/(2D),\widehat R_i(x)\}-R_i(x)\right).$$
--   For $r=1$, $f=\phi_1$ and the right-hand gap is $d(x,y)/(2D)-R_1(x)$. In particular, the subtraction lies outside the minimum and negative right sides are allowed. The constants depend only on the common collapse constants, and never on $D,r,X$ or the sets. This is the estimate used to combine terminal maps.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - generalization: unspecified absolute C and Ω constants → C=max(1,2√2 b) and c=min(1,a/2) for any supplied hyperplane-collapse map with constants a,b; reason: the proof on p. 9 gives two component Lipschitz contributions and at most two nonzero components; its lower-bound chain gives a/2, and the r=1 convention permits the displayed clipping; the explicit form implies the source's asymptotic statement
--   - encoding: ℓ₂ direct sum and the formal infinite R̂₁ convention → PiLp 2 (fun _ : Fin r => H2), with the singleton branch defined before heights; reason: a finite nonzero Hilbert sum is isometric to H2, and min(q,∞)=q is encoded without infinite arithmetic
--   - generalization: the setting after the finite-space reduction on p. 5 → arbitrary metric spaces and nonempty, possibly nonclosed subsets; reason: the proof on p. 9 explicitly treats noncompact subsets by approximating their infimal distance, and the remaining estimates are pointwise
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 8–9, Theorem 2.6

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_VoronoiModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Theorem 2.6 for the fixed map; the subtraction is OUTSIDE min, pp.8--9. -/
theorem theorem_2_6 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ψ : H2 → ℝ → H2) (hψ : HyperplaneCollapse a b ψ)
    (X : Type*) [MetricSpace X] (r : ℕ) (hr : 1 ≤ r) (D : ℝ) (hD : 1 ≤ D)
    (V : Fin r → Set X) (φ : Fin r → X → H2)
    (hφ : ∀ i, Terminal (V i) D (φ i)) :
    LipOn (max 1 (2*Real.sqrt 2*b)) (voronoiMap V φ ψ) Set.univ ∧
    ∀ i x, x ∈ cell V i → ∀ y,
      min 1 (a/2) * gap V D i x y ≤
        dist (voronoiMap V φ ψ x) (voronoiMap V φ ψ y) := by sorry

end BourgainUnion.Euclidean
