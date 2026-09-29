-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv
-- name    : AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a6d3ffc2-f67b-5766-a5b9-1ca1f6e95bd8
-- title:
--   Archimedean bi-finiteness of convolution kernels on GL₂(A_F)
-- statement:
--   Let $F$ be a number field, and let $f,f'\colon GL_2(\mathbb{A}_F)\to\mathbb{C}$ be functions on the group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$. Let `tys`, `tys'` be archimedean type families for $F$, each consisting of a function assigning to every infinite place $w$ of $F$ a natural number $\mathrm{card}(w)$ together with, for every $i < \mathrm{card}(w)$, a datum `ArchRepAt F w`, namely a natural number $n$ and a complex representation of `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$. Assume $f$ is continuous with compact support and `IsArchBiFinite F tys f` holds, i.e. $x\mapsto f(x^{-1})$ lies in `archCutSubmodule F tys`, the intersection over all infinite places $w$ of the sum over $i < \mathrm{card}(w)$ of the submodules `archTypeSubmoduleAt F w (tys.rep w i)`, while $f$ itself lies in the corresponding intersection-of-sums `archDualCutSubmodule F tys` built from the submodules `archDualTypeSubmoduleAt`; assume the same of $f'$ with respect to `tys'`. The conclusion is that there exists some archimedean type family `tys''` for $F$ such that `IsArchBiFinite F tys''` holds for the function `rightConv F f' (fun x => f x⁻¹)`, whose value at $g$ is $\int f'(gx)\,f(x^{-1})\,dx$ against the Haar measure `adelicGLHaar` on $GL_2(\mathbb{A}_F)$ for the Borel structure `glBorel`. The family `tys''` is only asserted to exist; no relation of it to `tys` and `tys'` is claimed.
--
--   This is the adelic $GL_2$ form of the classical stability of $K$-finiteness under convolution at the archimedean places: the kernel obtained by convolving two archimedean-bi-finite test functions is again bi-finite for some finite family of archimedean types. It is used by [`AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv`](thm.html#AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv) in the construction of test functions adapted to a cuspidal constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm

theorem AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hbf : IsArchBiFinite F tys f)
    (hfc' : Continuous f') (hfs' : HasCompactSupport f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F, IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by sorry
