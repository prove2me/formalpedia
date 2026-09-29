-- Prove2me | Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
-- name    : AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f396e951-64b4-587e-ba29-94c2e05995e7
-- title:
--   Whittaker expansion over principal ideles of a cuspidal function
-- statement:
--   Let $F$ be a number field, and let $D\subseteq GL_2(\mathbb{A}_F)$, a family $U$ of subgroups of $GL_2(\mathbb{A}_F)$ indexed by ideals of $\mathcal{O}_F$, and $\mathrm{gen}$ assigning an element of $GL_2(\mathbb{A}_F)$ to each finite place be the data out of which `productionPinsOf` builds the carrier pins: the Borel structures and Haar measures on $GL_2(\mathbb{A}_F)$ and $\mathbb{A}_F$, with $Z=\top$ and with the adelic measure replaced by the Haar measure conditioned on the box `adelicBox F` (a fundamental domain for the lattice at the infinite places, times the integral finite adeles). Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on $F$, continuous and nontrivial, and let $\varphi\colon GL_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous, invariant under left multiplication by the image of $GL_2(F)$ under entrywise $F\to\mathbb{A}_F$, a smooth vector for right translation by the kernel of the archimedean projection, and such that for each $g$ the map $z\mapsto\varphi\!\left(\begin{pmatrix}1&z\\0&1\end{pmatrix}g\right)$ on the mixed space of $F$ is $C^{[F:\mathbb{Q}]+1}$; assume moreover the vanishing $\int \varphi\!\left(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right)d\nu(x)=0$ of the Whittaker coefficient at $\alpha=0$ for every $g$. Then for every $g$ the family $\gamma\mapsto W_1(\mathrm{diag}(\gamma,1)g)$, indexed by the subgroup of principal ideles (the image of $F^\times$ in $\mathbb{A}_F^\times$), is summable with sum $\varphi(g)$, where $W_1(h)=\int\varphi\!\left(\begin{pmatrix}1&x\\0&1\end{pmatrix}h\right)\psi(-x)\,d\nu(x)$.
--
--   This is the Whittaker–Fourier expansion of a cusp form on $GL_2$ over a number field, written with the sum reindexed over the group of principal ideles so that it can be fed into integrals over a fundamental domain for $F^\times$. It is used in the Rankin–Selberg material and in the statements producing a $g$ at which the first Whittaker coefficient is nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped Classical in

theorem AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hsm : IsKfSmooth F φ)
    (harch : ∀ g : AdelicGL2 (𝓞 F) F,
      ContDiff ℝ (Module.finrank ℚ F + 1) (fun z : mixedEmbedding.mixedSpace F =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * g)))
    (hcusp : ∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g = 0)
    (g : AdelicGL2 (𝓞 F) F) :
    HasSum (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * g))
      (φ g) := by sorry
