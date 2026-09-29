-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
-- name    : AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/f27756bb-91e0-52ce-9527-eec75a9644b2
-- title:
--   Factorisable test functions are continuous and compactly supported
-- statement:
--   Let $F$ be a number field and let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on the general linear group of degree $2$ over the adele ring of $F$ (formed from the ring of integers $\mathcal{O}_F$ and $F$). Assume [`AutomorphicForm.IsFactorizableTestFn F f`](def/AutomorphicForm_FactorizableTestFn.html#L38), that is: there are functions $f_\infty : \mathrm{GL}_2(F_\infty) \to \mathbb{C}$ on the group over the infinite adele ring and $f_{\mathrm{f}} : \mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}}) \to \mathbb{C}$ on the group over the finite adele ring such that, first, $f_\infty$ factors as $f_\infty(g) = \Phi(\mathrm{archEntries}\,F\,g)$ for some function $\Phi$ on $2 \times 2$ matrices with entries in the mixed space of $F$ which is $C^\infty$ over $\mathbb{R}$ (`ContDiff ℝ ⊤`), $\mathrm{archEntries}\,F$ being the map recording the matrix entries of an element of $\mathrm{GL}_2(F_\infty)$ in that mixed space, and $f_\infty$ has compact support; second, $f_{\mathrm{f}}$ is locally constant and has compact support; and third, $f(g) = f_\infty(\mathrm{glArch}\,\mathcal{O}_F\,F\,g) \cdot f_{\mathrm{f}}(\mathrm{glFin}\,\mathcal{O}_F\,F\,g)$ for every $g$, where `glArch` and `glFin` are the group homomorphisms $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(F_\infty)$ and $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_F^{\mathrm{f}})$ obtained by applying the projections of the adele ring onto its archimedean and finite parts entrywise. Then $f$ is continuous and has compact support.
--
--   This is the basic regularity statement for the space of factorisable test functions on $\mathrm{GL}_2(\mathbb{A}_F)$: membership in the class used to define adelic automorphic forms guarantees the two analytic properties (continuity and compactness of the support) needed to integrate such functions against Haar measure and to average them over arithmetic subgroups. It is invoked throughout the construction of the adelic automorphic representation attached to a modular form, for instance in the estimates on class sums and in the analysis of cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

theorem AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f := by sorry
