-- Prove2me | Theorems.Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
-- name    : AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/bb4aacc1-9842-56fc-96b8-4dfbf99fc7c2
-- title:
--   Bessel's inequality for Whittaker coefficients on the adelic box
-- statement:
--   Let $F$ be a number field, and let there be given a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, and a family $\mathrm{gen}$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the height-one primes of $\mathcal{O}_F$; these are assembled, together with the Borel $\sigma$-algebras and Haar measures on $\mathrm{GL}_2(\mathbb{A}_F)$ and $\mathbb{A}_F$, the full subgroup of $\mathbb{A}_F^\times$ and the box $B \subseteq \mathbb{A}_F$ (the set of adeles whose infinite part lies in the fundamental domain of the lattice basis of the mixed space and whose finite part is everywhere integral), into the record `productionPinsOf F D U gen (adelicBox F)`; the only component of it that enters the conclusion is its measure $\nu$ on $\mathbb{A}_F$, namely the adelic additive Haar measure conditioned on the box. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on the image of $F$, continuous and non-trivial; let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$ be such that $u \mapsto \varphi(n(u)g)$ is continuous on $\mathbb{A}_F$, where $n(u)$ is the upper unipotent matrix $\begin{pmatrix} 1 & u \\ 0 & 1\end{pmatrix}$; and let $A$ be a finite subset of $F$. Writing $W_\alpha(\varphi)(g) = \int \varphi(n(x)g)\,\psi(-\alpha x)\, d\nu(x)$ for $\alpha \in F$, the assertion is $$\sum_{\alpha \in A} |W_\alpha(\varphi)(g)|^2 \le \int |\varphi(n(u)g)|^2 \, d\nu(u).$$
--
--   This is Bessel's inequality in $L^2(\nu)$ for the family of functions $u \mapsto \psi(\alpha u)$, $\alpha \in F$, applied to the unipotent slice of $\varphi$ through $g$; it bounds finitely many Fourier–Whittaker coefficients by the mean square of the slice over the box, with no summability or periodicity assumption on $\varphi$. It feeds the growth estimates for class sums and the window-mass comparisons for members of isotypic cuspidal submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : AdeleRing (𝓞 F) F => φ (unipotentGL2 u * g))
    (A : Finset F) :
    ∑ α ∈ A, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 ≤
      ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν := by sorry
