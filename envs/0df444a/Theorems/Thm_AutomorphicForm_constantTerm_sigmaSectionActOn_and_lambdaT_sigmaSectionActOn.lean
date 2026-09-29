-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
-- name    : AutomorphicForm.constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/62ea8efc-def5-5731-9381-9d609c745ead
-- title:
--   Constant term and truncation commute with the Galois twist
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idele Galois descent datum for $L/K$, i.e. a monoid homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L` that is continuous for each argument and satisfies $D.\mathrm{act}(g)(\iota(x)) = \iota(g x)$ on principal adeles, and let $\sigma \in \mathrm{Aut}_K(L)$. Fix furthermore a set $Dset$ of adelic matrices, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_L)$ indexed by ideals of $\mathcal{O}_L$, and a family $gen$ of adelic matrices indexed by the height-one spectrum of $\mathcal{O}_L$; these three enter only as fields of the carrier-pins record `productionPinsOf L Dset U gen (adelicBox L)`, of which the statement uses only the Borel structure `nS` on $\mathbb{A}_L$ and the measure $\nu$, the additive adelic Haar measure conditioned on the adelic box (archimedean box times the integral finite adeles). Let $u : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ satisfy $u(n(k) x) = u(x)$ for every $k \in L$ and every $x$, where $n(k) = \begin{pmatrix}1&k\\0&1\end{pmatrix}$ is the image of the rational unipotent matrix under `globalPoints`. Write $\sigma_{\mathbb{A}}$ for the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}(\sigma)$ entrywise, $\mathrm{CT}(\varphi)(g) = \int \varphi(n(t) g)\, d\nu(t)$ with $n(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$ for $t \in \mathbb{A}_L$, and $\Lambda^T \varphi(g) = \varphi(g) - \mathbf{1}_{\{H > T\}}(g)\,\mathrm{CT}(\varphi)(g)$ with $H$ the adelic height of $L$. The conclusion is the conjunction: for every $g$, $\mathrm{CT}(u \circ \sigma_{\mathbb{A}})(g) = \mathrm{CT}(u)(\sigma_{\mathbb{A}} g)$; and for every real $T$ and every $g$, $\Lambda^T(u \circ \sigma_{\mathbb{A}})(g) = \Lambda^T(u)(\sigma_{\mathbb{A}} g)$.
--
--   This is the equivariance of the one-cusp constant term and of Arthur's truncation operator on $\mathrm{GL}_2$ under the Galois twist of functions coming from a descent datum on the adeles, the height entering the truncation being $\sigma_{\mathbb{A}}$-invariant by [`AutomorphicForm.adelicHeight_sigmaAdelicAct`](thm.html#AutomorphicForm.adelicHeight_sigmaAdelicAct). It is used in the trace-formula computations that compare truncated integrals of twisted automorphic functions with their untwisted counterparts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (Dset : Set (AdelicGL2 (𝓞 L) L)) (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L))
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : ∀ (k : L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L (unipotentGL2 k) * x) = u x) :
    (∀ g : AdelicGL2 (𝓞 L) L,
      @AutomorphicForm.constantTerm _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          (sigmaSectionActOn K L D σ u) g =
        @AutomorphicForm.constantTerm _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          u (sigmaAdelicAct K L D σ g)) ∧
    ∀ (T : ℝ) (g : AdelicGL2 (𝓞 L) L),
      @AutomorphicForm.lambdaT _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T (sigmaSectionActOn K L D σ u) g =
        @AutomorphicForm.lambdaT _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T u (sigmaAdelicAct K L D σ g) := by sorry
