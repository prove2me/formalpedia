-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
-- name    : AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c0ab96a4-eaa6-540b-9a2a-4c6cd653c59a
-- title:
--   Right convolutions commute at one irreducible archimedean type
-- statement:
--   Let $F$ be a number field and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. Let $U \le G$ be a subgroup whose underlying set is compact, let $O \le G$ be a subgroup whose underlying set is open, and assume $U = O \sqcap \ker(\mathrm{glArch})$, the meet of $O$ with the subgroup `finiteAdelicGL2Subgroup F` of elements with trivial archimedean component. For each infinite place $w$ let $\tau_w$ be an `ArchRepAt F w`, that is a natural number $n$ together with a representation $\rho$ of `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$, and assume each $\rho$ is irreducible. Let $\langle 1, \tau\rangle$ denote the archimedean type family with exactly one type, namely $\tau_w$, at each infinite place $w$. Let $f : G \to \mathbb{C}$ be level-spherical of type $\langle 1, \tau\rangle$ at $U$: there is $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ which is an archimedean test factor (given by a smooth function of the matrix entries and of compact support), is archimedean-factor bi-finite of type $\langle 1,\tau\rangle$, is invariant under conjugation by $\mathrm{archRowIsometryInclAt₀}(w,k)$ for every infinite place $w$ and every $k$ in the row-isometry subgroup at $w$, and satisfies $f(g) = f_\infty(\mathrm{glArch}\,g)\cdot \mathbf{1}_{\mathrm{glFin}(U)}(\mathrm{glFin}\,g)$ for all $g$. Let $h : G \to \mathbb{C}$ be a factorizable test function, i.e. $h(g) = h_\infty(\mathrm{glArch}\,g)\,h_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $h_\infty$ an archimedean test factor and $h_{\mathrm{fin}}$ locally constant of compact support; assume $h$ is archimedean bi-finite of type $\langle 1,\tau\rangle$ (i.e. $x \mapsto h(x^{-1})$ lies in the archimedean cut submodule and $h$ in the dual one for that family) and bi-$U$-invariant, $h(ux) = h(x) = h(xu)$ for all $x \in G$, $u \in U$. Finally let $\varphi : G \to \mathbb{C}$ be continuous. Then $(\varphi * f) * h = (\varphi * h) * f$, where the right convolution is $(\psi * k)(g) = \int_G \psi(gx)k(x)\,d\mu(x)$ for the adelic Haar measure $\mu$ on $G$.
--
--   This is the commutation of the two right-convolution (Hecke) operators attached to $f$ and $h$, applied to an arbitrary continuous function $\varphi$, for an arbitrary compact level $U$ cut out of an open subgroup by the condition of trivial archimedean part. It is used in the construction of commuting lifts of convolution operators on the cuspidal spectrum, via [`AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f := by sorry
