-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
-- name    : AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/8efd6045-5770-5245-ac83-458cd51eb427
-- title:
--   Replacing a test function by an archimedean bi-finite one
-- statement:
--   Let $F$ be a number field and let $tys$ be a family of archimedean types, that is, data assigning to each infinite place $w$ of $F$ a natural number $\mathrm{card}\,w$ and, for each index $i < \mathrm{card}\,w$, a representation of the subgroup $\mathrm{rowIsometrySubgroup}_0$ of $\mathrm{GL}_2(F_w)$ on some $\mathbb{C}^n$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and lie in the submodule $\mathrm{archCutSubmodule}$ attached to $tys$, i.e. in the intersection over all infinite places $w$ of the sum over $i$ of the type submodules $\mathrm{typeSubmodule}$ for the inclusion $\mathrm{rowIsometryInclAt}_0$ at $w$ and the representation $tys.\mathrm{rep}\,w\,i$. Let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a factorizable test function: $f(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for some compactly supported $f_\infty$ on $\mathrm{GL}_2(F_\infty)$ which is a $C^\infty$ function of the archimedean matrix entries, and some locally constant compactly supported $f_{\mathrm{fin}}$ on $\mathrm{GL}_2(\mathbb{A}_{F,\mathrm{fin}})$. Assume $\mathrm{rightConv}\,\varphi\,f = \lambda \cdot \varphi$ for some $\lambda \in \mathbb{C}$, where $(\mathrm{rightConv}\,\varphi\,f)(g) = \int \varphi(gx) f(x)\,dx$ against the Haar measure $\mathrm{adelicGLHaar}$ on $\mathrm{GL}_2(\mathbb{A}_F)$ for its Borel structure. Then there exists a factorizable test function $f'$ which is moreover archimedean bi-finite for $tys$, meaning that $g \mapsto f'(g^{-1})$ lies in $\mathrm{archCutSubmodule}$ for $tys$ and $f'$ itself lies in the corresponding $\mathrm{archDualCutSubmodule}$, and which satisfies the same eigenvalue equation $\mathrm{rightConv}\,\varphi\,f' = \lambda \cdot \varphi$.
--
--   This is the standard device of replacing a smoothing test function by one sandwiched between idempotents of the archimedean Hecke algebra, so that the eigenfunction equation is preserved while the test function acquires prescribed types on both sides. It is used in the analysis of cuspidal constituents of forms lying in a given archimedean cut, and in the Langlands–Tunnell step, where isotypic cusp forms that are eigenvectors for right convolution are decomposed into constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφt : φ ∈ archCutSubmodule F tys)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ)
    (heig : rightConv F φ f = lam • φ) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      rightConv F φ f' = lam • φ := by sorry
