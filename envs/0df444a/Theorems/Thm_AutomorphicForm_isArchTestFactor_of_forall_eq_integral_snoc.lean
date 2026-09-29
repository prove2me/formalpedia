-- Prove2me | Theorems.Thm_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc
-- name    : AutomorphicForm.isArchTestFactor_of_forall_eq_integral_snoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/22c50d19-9dfc-5170-94e4-85e62f12b2d5
-- title:
--   Fibre integrals along multiplication give archimedean test factors
-- statement:
--   Let $K$ be a number field and write $G = \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for the general linear group of degree $2$ over the infinite adele ring of $K$, equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be a measure on $G$ that is finite on compact sets. Let $n$ be a natural number and let $\Phi \colon G^{n+1} \to \mathbb{C}$ (functions on `Fin (n+1) → G`) satisfy two conditions: first, $\Phi$ factors through the matrix entries read in the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ of $K$, in the sense that there is a map $\Psi$ on $(n+1)$-tuples of $2 \times 2$ matrices over `mixedEmbedding.mixedSpace K` which is $C^\infty$ as a map of real vector spaces and satisfies $\Phi(x) = \Psi\bigl(k \mapsto \mathrm{archEntries}\,K\,(x_k)\bigr)$ for all $x$, where `archEntries` sends $g$ to the matrix of its entries transported by the ring isomorphism from the infinite adele ring to the mixed space; and second, $\Phi$ has compact support. Let $f \colon G \to \mathbb{C}$ be such that for every $h$, $$f(h) = \int_{c \in G^{n}} \Phi\bigl(c_0,\dots,c_{n-1}, (c_0 \cdots c_{n-1})^{-1} h\bigr)\, d\mu^{\otimes n}(c),$$ the inverse being that of the ordered product of the coordinates of $c$ and the last argument being appended by `Fin.snoc`. Then $f$ satisfies `IsArchTestFactor K`, i.e. there is a $C^\infty$ function $\Phi_0$ on $2 \times 2$ matrices over the mixed space with $f(g) = \Phi_0(\mathrm{archEntries}\,K\,g)$ for all $g$, and $f$ has compact support.
--
--   This supplies the archimedean component of a factorizable test function: pushing a smooth compactly supported function on $G^{n+1}$ forward along the multiplication map $G^{n+1} \to G$ by integration over the fibres again yields a smooth compactly supported function of the archimedean matrix entries. It is used in the construction of matching test functions at the archimedean places, by [`AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom`](thm.html#AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory
open scoped Classical

theorem AutomorphicForm.isArchTestFactor_of_forall_eq_integral_snoc
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ)
    (hΦs : ∃ Ψ : (Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, Φ x = Ψ (fun k => AutomorphicForm.archEntries K (x k)))
    (hΦc : HasCompactSupport Φ)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    AutomorphicForm.IsArchTestFactor K f := by sorry
