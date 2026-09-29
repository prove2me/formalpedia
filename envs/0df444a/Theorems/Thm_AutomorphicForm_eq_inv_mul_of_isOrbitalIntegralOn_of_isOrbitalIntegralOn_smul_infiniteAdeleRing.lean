-- Prove2me | Theorems.Thm_AutomorphicForm_eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing
-- name    : AutomorphicForm.eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/d890d4ec-d1d0-5909-9f1c-f07aea5e594b
-- title:
--   Archimedean orbital integrals scale inversely with centraliser Haar measure
-- statement:
--   Let $K$ be a number field and let $\gamma \in \mathrm{GL}_2(\mathbb{A}_{K,\infty})$, where $\mathbb{A}_{K,\infty} = \mathrm{InfiniteAdeleRing}\,K$, be regular semisimple in the sense that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $\mathbb{A}_{K,\infty}$. Let $\nu$ be a Haar measure on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), and $\tau$ a Haar measure on the centraliser $Z = \mathrm{Subgroup.centralizer}\,\{\gamma\}$ for its Borel $\sigma$-algebra. Let $c > 0$ be real, and let $f : \mathrm{GL}_2(\mathbb{A}_{K,\infty}) \to \mathbb{C}$ be an archimedean test factor, i.e. $f$ has compact support and there is a $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $K$ with $f(g) = \Phi(\mathrm{archEntries}\,g)$ for all $g$, the entries of $g$ being transported to the mixed space by the canonical ring equivalence. Suppose $I, I' \in \mathbb{C}$ are orbital-integral values for $f$ at $\gamma$ with respect to $(\nu,\tau)$ and to $(\nu, \mathrm{ENNReal.ofReal}\,c \cdot \tau)$ respectively; that is, in each case there is a weight $w \ge 0$, measurable with compact support, satisfying $\int_{Z} w(tx)\,\mathrm{d}(\text{measure}) = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$, and the value equals $\int f(x^{-1}\gamma x)\,w(x)\,\mathrm{d}\nu$. Then $I' = c^{-1} I$.
--
--   This is the change-of-measure law for archimedean orbital integrals: rescaling the Haar measure on the centraliser of a regular semisimple element rescales the orbital-integral value inversely; the case $c = 1$ gives independence of the chosen section weight. It feeds the archimedean bookkeeping in the comparison of orbital and twisted orbital integrals and in the window computations that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] AutomorphicForm.centralizerBorel

theorem AutomorphicForm.eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) [τ.IsHaarMeasure]
    (c : ℝ) (hc : 0 < c)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : AutomorphicForm.IsArchTestFactor K f)
    (I I' : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν γ τ f I)
    (hI' : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν γ (ENNReal.ofReal c • τ) f I') :
    I' = (c : ℂ)⁻¹ * I := by sorry
