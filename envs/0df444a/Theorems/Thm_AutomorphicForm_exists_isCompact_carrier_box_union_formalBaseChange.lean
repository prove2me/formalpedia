-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_carrier_box_union_formalBaseChange
-- name    : AutomorphicForm.exists_isCompact_carrier_box_union_formalBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/7c673353-159e-5477-85a8-3cd522f2ce71
-- title:
--   A compact carrier for Satake boxes and their formal base change
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S_K$ and $S_L$ be finite sets of height-one primes of $\mathcal{O}_K$ and $\mathcal{O}_L$, let $\xi_L$ be a homomorphism from the full subgroup of units of the adele ring of $L$ to $\mathbb{C}^\times$, and let $\Xi$ be a finite set of such homomorphisms for $K$. For a field $F$ among these, a homomorphism $\xi$ and the corresponding finite set $S$, call a function $x$ from the height-one primes of $\mathcal{O}_F$ to $\mathbb{C}\times\mathbb{C}$ admissible if $x_v=0$ for $v\in S$ and, for $v\notin S$, writing $\gamma_v=\xi(\det(\mathtt{heckeGen}\,v))$: $(x_v)_2=N(v)\,\gamma_v$ with $N(v)$ the absolute norm of $v$, $\|(x_v)_1\|\le (N(v)+1)\sqrt{\|\gamma_v\|}$, and $\overline{(x_v)_1}=\bigl(\overline{(x_v)_2}/\|(x_v)_2\|\bigr)(x_v)_1$. The theorem asserts the existence of a compact set $X$ of functions from the height-one primes of $\mathcal{O}_L$ to $\mathbb{C}\times\mathbb{C}$ such that: the admissible set for $(L,\xi_L,S_L)$ is contained in $X$; for every homomorphism $\xi_K$ whatsoever the admissible set for $(K,\xi_K,S_K)$ is compact; for each $\xi_K\in\Xi$ and each admissible $x$ over $K$, the function sending $w$ to $\bigl(\mathtt{satakePow}\,f\,(x_u)_1\,(x_u)_2,\;(x_u)_2^{\,f}\bigr)$ lies in $X$, where $u$ is the prime of $\mathcal{O}_K$ under $w$ and $f$ is the inertia degree of $u$ in $w$, and $\mathtt{satakePow}$ is given by $p_0=2$, $p_1=s$, $p_{n+2}=s\,p_{n+1}-e\,p_n$; every $y\in X$ satisfies $\overline{(y_w)_1}=\bigl(\overline{(y_w)_2}/\|(y_w)_2\|\bigr)(y_w)_1$ at every $w$; and for each $w$ the set of second coordinates $\{(y_w)_2:y\in X\}$ is finite.
--
--   The sets described are the boxes of Satake data cut out by the unitarity and Ramanujan-type bounds at the unramified places, together with the formal unramified base-change map on such data, expressed through the recursion for power sums of the Satake parameters. The result packages them inside a single compact set with finitely many possible second coordinates at each place, and is used in the comparison of fibre sums of twisted and untwisted cut traces in [`AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_docks_ed2`](thm.html#AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_docks_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_carrier_box_union_formalBaseChange.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate NumberField

theorem AutomorphicForm.exists_isCompact_carrier_box_union_formalBaseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)) :
    ∃ X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ), IsCompact X ∧
      {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X ∧
      (∀ ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, IsCompact
        {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1}) ∧
      (∀ ξK ∈ Ξ, ∀ x ∈ {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1},
        (fun w : HeightOneSpectrum (𝓞 L) =>
        (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
            (x (HeightOneSpectrum.under (𝓞 K) w)).1 (x (HeightOneSpectrum.under (𝓞 K) w)).2,
          (x (HeightOneSpectrum.under (𝓞 K) w)).2 ^
            (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)) ∈ X) ∧
      (∀ y ∈ X, ∀ w : HeightOneSpectrum (𝓞 L),
        conj (y w).1 = conj (y w).2 / ((‖(y w).2‖ : ℝ) : ℂ) * (y w).1) ∧
      (∀ w : HeightOneSpectrum (𝓞 L),
        ((fun y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ => (y w).2) '' X).Finite) := by sorry
