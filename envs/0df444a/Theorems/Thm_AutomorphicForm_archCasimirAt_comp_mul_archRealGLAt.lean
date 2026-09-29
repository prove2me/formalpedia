-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt
-- name    : AutomorphicForm.archCasimirAt_comp_mul_archRealGLAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/79c2b3ff-c081-5d45-aa77-2fea48bc2397
-- title:
--   Archimedean Casimir commutes with right translation by GL₂(ℝ)
-- statement:
--   Let $K$ be a number field, let $w$ be an infinite place of $K$ with $w$ real, and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $K$ (that is, on `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring). Write $\iota_w =$ `archRealGLAt hw` for the group homomorphism $\mathrm{GL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{A}_K)$ obtained by transporting matrices along the inverse of the ring isomorphism $K_w \cong \mathbb{R}$ attached to the real place $w$ and then including $\mathrm{GL}_2(K_w)$ into the adelic group at $w$. Assume $\varphi$ satisfies `IsArchSmoothAt hw`, i.e. for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ the function $e \mapsto \varphi(g \cdot \iota_w(e))$ of a real $2 \times 2$ matrix $e$ is $C^\infty$ on the open set where $\det e \neq 0$ (with $\iota_w$ extended by $1$ off that set). Let $k \in \mathrm{GL}_2(\mathbb{R})$. Then the operator `archCasimirAt hw`, namely $\Omega_w = -\bigl(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_{F^-}\bigr)$ where $D_d\psi(g)$ is the derivative at $t = 0$ of $t \mapsto \psi(g \cdot \mathrm{archFlowAt}\,hw\,d\,t)$ for the three archimedean directions $H$, $E$, $F^-$, satisfies $\Omega_w\bigl(x \mapsto \varphi(x\,\iota_w(k))\bigr) = \bigl(x \mapsto (\Omega_w \varphi)(x\,\iota_w(k))\bigr)$ as functions on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the centrality of the Casimir element of the universal enveloping algebra of $\mathfrak{gl}_2(\mathbb{R})$, in the concrete form that the Casimir differential operator at a real place commutes with right translation by elements of $\mathrm{GL}_2(\mathbb{R})$ placed at that place. It is used in the construction of a Casimir eigenvector of minimal weight inside a continuous realization, in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.archCasimirAt_comp_mul_archRealGLAt
    {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) :
    archCasimirAt hw (fun x => φ (x * archRealGLAt hw k)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw k) := by sorry
