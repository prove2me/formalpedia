-- Prove2me | Theorems.Thm_AutomorphicForm_apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
-- name    : AutomorphicForm.apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7f579e85-79ae-5326-8aad-07495807e96b
-- title:
--   Vanishing unipotent derivatives force right SL₂(ℝ)-invariance at a real place
-- statement:
--   Let $F$ be a number field, $w$ a real infinite place of $F$ (so $w$ satisfies `InfinitePlace.IsReal`), and let $\varphi$ be a complex-valued function on the adelic group $\mathrm{GL}_2(\mathbb{A}_F)$, realised as `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over the adele ring of $F$. Assume `IsArchSmoothAt hw φ`: for every $g$ in $\mathrm{GL}_2(\mathbb{A}_F)$ the function sending a real $2\times2$ matrix $e$ to $\varphi(g\cdot\,$`archRealLiftAt hw e`$)$ is $C^\infty$ on the open set of $e$ with $\det e\neq 0$, where `archRealLiftAt hw e` places an invertible $e$ into the $w$-component of $\mathrm{GL}_2(\mathbb{A}_F)$ via the identification of $w$'s completion with $\mathbb{R}$ (and is $1$ when $\det e=0$). Assume further that the directional derivatives at $w$ in the directions `ArchDir.E` and `ArchDir.Fm` vanish identically as functions on $\mathrm{GL}_2(\mathbb{A}_F)$, i.e. for every $g$ the derivative at $t=0$ of $t\mapsto\varphi(g\cdot\,$`archFlowAt hw d t`$)$ is $0$ for $d=$ `E` and $d=$ `Fm`. Then for every $g$ in $\mathrm{GL}_2(\mathbb{A}_F)$ and every $h$ in $\mathrm{GL}_2(\mathbb{R})$ with $\det h=1$, one has $\varphi(g\cdot\,$`archRealGLAt hw h`$)=\varphi(g)$, where `archRealGLAt hw` is the homomorphism $\mathrm{GL}_2(\mathbb{R})\to\mathrm{GL}_2(\mathbb{A}_F)$ given by transporting along the inverse of the ring isomorphism $w$-completion $\cong\mathbb{R}$ and then including at the place $w$. No hypothesis is imposed on the derivative in the direction `ArchDir.H`.
--
--   This is the elementary half of the principle that a smooth vector annihilated by the Lie algebra is fixed by the connected group: annihilation by the two unipotent directions at a real place already gives right invariance under the determinant-one subgroup placed at that place. It is used in the analysis of archimedean behaviour of cuspidal constituents, in particular by the results on Casimir eigenvalues for cusp constituents and by the lower bound for archimedean occurrence of lowering-annihilated forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (hE : archDerivAt hw .E φ = 0) (hF : archDerivAt hw .Fm φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archRealGLAt hw h) = φ g := by sorry
