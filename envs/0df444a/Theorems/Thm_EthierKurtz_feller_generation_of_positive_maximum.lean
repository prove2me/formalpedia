-- Prove2me | Theorems.Thm_EthierKurtz_feller_generation_of_positive_maximum
-- name    : EthierKurtz.feller_generation_of_positive_maximum
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T18:59:51.297001+00:00
-- url     : https://prove2.me/theorems/60ce9994-06ae-4c31-8373-e426899275cd
-- title:
--   Theorem 4.2.2 — Feller generation from the positive maximum principle (compact state space)
-- statement:
--   Let $X$ be a compact topological space and let $A$ be a linear operator on $C(X)$ (with the supremum norm), given by its graph $G\subseteq C(X)\times C(X)$, a linear subspace. Assume:
--
--   1. **Positive maximum principle:** whenever $(f,g)\in G$ and $x\in X$ satisfy $f(x)=\sup_y f(y)\ge 0$, then $g(x)\le 0$;
--
--   2. **Dense domain:** $\mathcal D(A)=\{f : (f,g)\in G\}$ is dense in $C(X)$;
--
--   3. **Range condition:** for some $r>0$ the range $\{rf-g : (f,g)\in G\}$ of $r-A$ is dense in $C(X)$;
--
--   4. $(1,0)$ lies in the closure $\overline{G}$ of the graph.
--
--   Then there is a strongly continuous contraction semigroup $(T(t))_{t\ge0}$ on $C(X)$ which is positive ($f\ge 0\Rightarrow T(t)f\ge 0$), conservative ($T(t)1=1$), and whose infinitesimal generator is exactly $\overline{G}$: for all $f,g\in C(X)$,
--
--   $$\lim_{t\downarrow 0}\frac{T(t)f-f}{t}=g \iff (f,g)\in\overline{G}.$$
--
--   This is the Hille–Yosida theorem for Feller semigroups in the compact case, together with the standard conservativity remark.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 4, Section 2, Theorem 2.2 (printed p. 165) and the remark on conservative semigroups following it; Hille–Yosida theorem Chapter 1, Theorem 2.6.

import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology

namespace EthierKurtz

/-- Ethier–Kurtz, Chapter 4, Theorem 2.2 (compact state space), together with the
conservativity statement: a linear operator on `C(X)` with dense domain satisfying
the positive maximum principle, for which `r - A` has dense range for some `r > 0`,
has a closure that generates a positive strongly continuous contraction semigroup;
if `(1, 0)` lies in the closure, the semigroup is conservative. -/
theorem feller_generation_of_positive_maximum {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (hdense : Dense (Prod.fst '' (G : Set (C(X, ℝ) × C(X, ℝ)))))
    (hrange : ∃ r : ℝ, 0 < r ∧
      Dense ((fun fg : C(X, ℝ) × C(X, ℝ) => r • fg.1 - fg.2) '' (G : Set _)))
    (hone : ((1 : C(X, ℝ)), (0 : C(X, ℝ))) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ)))) :
    ∃ T : ℝ → C(X, ℝ) →L[ℝ] C(X, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ)))) := by sorry
