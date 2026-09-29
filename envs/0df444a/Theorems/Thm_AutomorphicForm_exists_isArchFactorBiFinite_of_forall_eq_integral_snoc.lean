-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc
-- name    : AutomorphicForm.exists_isArchFactorBiFinite_of_forall_eq_integral_snoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/dc0b61fb-e4c3-5796-8efe-1eb3235aff9e
-- title:
--   Archimedean bi-finiteness of a fibre integral on GL₂
-- statement:
--   Let $K$ be a number field, write $K_\infty$ for `InfiniteAdeleRing K`, and equip $G = \mathrm{GL}_2(K_\infty)$ with a measurable structure that is the Borel structure of its topology; let $\mu$ be a left-invariant measure on $G$ which is finite on compact sets. Let $n$ be a natural number and $\Phi : G^{n+1} \to \mathbb{C}$ continuous with compact support, and let `tys` be an archimedean type family for $K$, that is, data assigning to each infinite place $w$ of $K$ a number `tys.card w` of types, each a finite-dimensional complex representation $\tau.\rho$ of `rowIsometrySubgroup₀` of the completion $K_w$. Assume that for every $x \in G^{n+1}$ the function $g \mapsto \Phi(x \text{ with } 0\text{-th entry } g^{-1})$ lies in `archFactorCutSubmodule K tys`, the intersection over all infinite places $w$ of the sum over $i < \mathrm{tys.card}\,w$ of the type submodules `typeSubmodule (archRowIsometryInclAt₀ K w) (tys.rep w i).ρ`, and that for every $x$ the function $g \mapsto \Phi(x \text{ with last entry } g)$ lies in the corresponding submodule `archFactorDualCutSubmodule K tys` formed from the dual representations $\rho^\vee$. Assume finally that $f : G \to \mathbb{C}$ satisfies $f(h) = \int_{c \in G^n} \Phi\bigl(c_0,\dots,c_{n-1},(c_0\cdots c_{n-1})^{-1}h\bigr)\, d\mu^{\otimes n}$ for all $h$. Then there exists an archimedean type family `tysK` for $K$ with `IsArchFactorBiFinite K tysK f`, i.e. $h \mapsto f(h^{-1})$ lies in the cut submodule of `tysK` and $f$ lies in its dual cut submodule. The family produced is not asserted to be `tys`.
--
--   This is the archimedean finiteness step for the fibre (convolution) integral: passing from finiteness of the archimedean types of $\Phi$ in its first and last variables to two-sided finiteness of the resulting function of one variable on $\mathrm{GL}_2(K_\infty)$. It is used in the construction of matching archimedean test data, through [`AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom`](thm.html#AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory

theorem AutomorphicForm.exists_isArchFactorBiFinite_of_forall_eq_integral_snoc
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (tys : AutomorphicForm.ArchTypeFamily K)
    (h0 : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x 0 g⁻¹)) ∈ AutomorphicForm.archFactorCutSubmodule K tys)
    (hn : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x (Fin.last n) g)) ∈
        AutomorphicForm.archFactorDualCutSubmodule K tys)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    ∃ tysK : AutomorphicForm.ArchTypeFamily K, AutomorphicForm.IsArchFactorBiFinite K tysK f := by sorry
