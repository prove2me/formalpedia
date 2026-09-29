-- Prove2me | Theorems.Thm_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
-- name    : AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/bd21a658-9a94-5d32-be64-a32610c18476
-- title:
--   Split coordinates on GL₂(L⊗_K A): shift, norm string, Haar
-- statement:
--   Let $K\subseteq L$ be fields with $L$ finite-dimensional over $K$, write $n=\mathrm{finrank}_K L$ and assume $n$ is prime; let $\sigma : L\simeq_{K} L$ be a $K$-algebra automorphism with $\sigma\neq 1$. Let $A$ be a commutative $K$-algebra carrying a topology making it a Hausdorff, locally compact, second countable topological ring, and let $\iota : L\to A$ be a $K$-algebra homomorphism. Both $\mathrm{GL}_2(L\otimes_K A)$ and $\mathrm{GL}_2(A)$ are equipped with the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) of their topologies; let $\mu_L$ and $\mu_A$ be Haar measures on these two groups. Let $\Psi=$ [`AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ`](def/AutomorphicForm_SplitFibreIntegral.html#L275) be the group isomorphism $\mathrm{GL}_2(L\otimes_K A)\simeq (\mathrm{Fin}((n-1)+1)\to \mathrm{GL}_2(A))$ obtained by applying the ring isomorphism `psiEquiv A σ ι hdeg hσ` built from $\iota$ and $\sigma$ entrywise to $2\times 2$ matrices, passing to units and matching the index type $\mathrm{Fin}\,n$ with $\mathrm{Fin}((n-1)+1)$. The conclusion is the conjunction of seven assertions: $\Psi$ is continuous; $\Psi^{-1}$ is continuous; for every $g$ and every index $j$, $\Psi(\sigma g)_j=\Psi(g)_{j+1}$, where $\sigma g$ denotes the image of $g$ under the map [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) induced by $\sigma\otimes\mathrm{id}_A$ and indices are added in $\mathrm{Fin}((n-1)+1)$; for every $g\in\mathrm{GL}_2(A)$ the coordinates of the image of $g$ under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) (induced by $a\mapsto 1\otimes a$) are all equal to $g$; for every $\delta$ and every $j$, the $j$-th coordinate of [`AutomorphicForm.normString K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L205) $=\delta\cdot\sigma\delta\cdots\sigma^{n-1}\delta$ equals the ordered product $\prod_{k}\Psi(\delta)_{j+k}$ over $k\in\mathrm{Fin}((n-1)+1)$ in increasing order of $k$; the case $j=0$ of this, stated as the ordered product of the list of all coordinates of $\Psi(\delta)$; and there exists $c\in\mathbb{R}_{\geq 0}$ with $c>0$ such that the pushforward of $\mu_L$ along $\Psi$ equals $c$ times the product measure $\prod_{j}\mu_A$ over $\mathrm{Fin}((n-1)+1)$.
--
--   This packages the local structure of a place of $K$ that splits completely in $L$: the coordinate isomorphism identifies $\mathrm{GL}_2(L\otimes_K A)$ with $n$ copies of $\mathrm{GL}_2(A)$, turns the Galois automorphism into a cyclic shift of coordinates, sends the norm string $\delta\,\sigma\delta\cdots\sigma^{n-1}\delta$ to ordered products of shifted coordinate strings, and transports Haar measure to a positive multiple of product Haar measure. It is used in the computation of integrals over semi-local integral sets and in the existence statements for twisted orbital integrals at the archimedean places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA) :
    letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
    Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) ∧
    Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ).symm ∧
    (∀ (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.sigmaGL K L A σ g) j =
        AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ g (j + 1)) ∧
    (∀ g : GL (Fin 2) A,
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.toTensorGL K L A g) = fun _ => g) ∧
    (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) j =
        (List.ofFn fun k : Fin (Module.finrank K L - 1 + 1) =>
          AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ (j + k)).prod) ∧
    (∀ δ : GL (Fin 2) (L ⊗[K] A),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) 0 =
        (List.ofFn (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ)).prod) ∧
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) μL =
        c • Measure.pi (fun _ : Fin (Module.finrank K L - 1 + 1) => μA) := by sorry
