-- Prove2me | Theorems.Thm_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
-- name    : AutomorphicForm.isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b2c0480f-db98-5a69-8600-2c1484d9d04b
-- title:
--   Compact (t,t⁻¹)-torus and its table map into X
-- statement:
--   Let $L$ be a number field, $S_L$ a finite set of nonzero primes of $\mathcal{O}_L$, and $\xi_L$ a monoid homomorphism from the full subgroup of the units of the adele ring of $L$ to $\mathbb{C}^\times$; write $\zeta_w$ for the value of $\xi_L$ at the determinant of the Hecke generator `heckeGen` at $w$, the element of $\mathrm{GL}_2$ of the adeles obtained from a uniformiser at $w$ through the local unit and the diagonal embedding. Let $X$ be a set of "tables", i.e. of functions from the primes of $\mathcal{O}_L$ to $\mathbb{C}\times\mathbb{C}$, assumed to contain every $x$ with $x_w=0$ for all $w\in S_L$ and, for $w\notin S_L$, $x_w^{(2)}=N(w)\,\zeta_w$ (here `HeckeEigensystem.cNorm` $w$ is the absolute norm of $w$ viewed in $\mathbb{C}$), $\|x_w^{(1)}\|\le (N(w)+1)\sqrt{\|\zeta_w\|}$ and $\overline{x_w^{(1)}}=\bigl(\overline{x_w^{(2)}}/\|x_w^{(2)}\|\bigr)\,x_w^{(1)}$. Let $d\in\mathbb{N}$, let $w':\mathrm{Fin}\,d\to$ primes be injective with $w'(i)\notin S_L$ for all $i$, and let $s:\mathrm{Fin}\,d\to\mathbb{C}$ satisfy $s_i^2=\zeta_{w'(i)}$. Then: (i) the range $T$ of $\theta\mapsto\bigl(i\mapsto(e(\theta_i),e(-\theta_i))\bigr)$, with $e(\pm\,\cdot)$ the characters `fourier 1` and `fourier (-1)` on $\mathbb{R}/\mathbb{Z}$, is compact in $\mathrm{Fin}\,d\to\mathbb{C}\times\mathbb{C}$; (ii) there is a continuous map from $\mathrm{Fin}\,d\to\mathbb{R}/\mathbb{Z}$ to the subtype $T$ whose $i$-th coordinate at $\theta$ is $(e(\theta_i),e(-\theta_i))$; (iii) for each $i$ the map $B_i(p_1,p_2)=\bigl(\sqrt{N(w'(i))}\,s_i(p_1+p_2),\;N(w'(i))\zeta_{w'(i)}+(p_1p_2-1)\bigr)$ on $\mathbb{C}\times\mathbb{C}$ is continuous; (iv) each $B_i$ has finite fibres, the preimage of every singleton being finite; and (v) there is a continuous map $bc$ from the subtype $T$ to $X$ such that for every $x\in T$ and every $i$ the table $bc(x)$ takes at $w'(i)$ the value $B_i$ applied to the $i$-th coordinate of $x$.
--
--   This assembles, in one statement, the concrete geometry needed to transport measures on the compact torus of tempered Satake parameters to the space of Hecke tables: compactness of the $(t,t^{-1})$-image of $(\mathbb{R}/\mathbb{Z})^d$, the parametrising map onto it, and the polynomial coordinate maps $B_i$, continuous with finite fibres, defining a continuous table-valued map into $X$. It is used in the construction of the cylinder functional without atomic mass, [`AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass`](thm.html#AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ComplexConjugate

theorem AutomorphicForm.isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
    (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (d : ℕ) (w' : Fin d → HeightOneSpectrum (𝓞 L)) (hw'S : ∀ i : Fin d, w' i ∉ SL)
    (hw'i : Function.Injective w')
    (s : Fin d → ℂ)
    (hs : ∀ i : Fin d, s i ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) :
    IsCompact (Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
      fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))) ∧
    (∃ emb : C((Fin d → AddCircle (1 : ℝ)), ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
        fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))),
      ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
        ((emb θ : ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
          fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))) : Fin d → ℂ × ℂ) i =
          ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))) ∧
    (∀ i : Fin d, Continuous (fun p : ℂ × ℂ =>
      (((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
        HeckeEigensystem.cNorm (w' i) *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
          (p.1 * p.2 - 1)) : ℂ × ℂ))) ∧
    (∀ (i : Fin d) (q : ℂ × ℂ), ((fun p : ℂ × ℂ =>
      (((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
        HeckeEigensystem.cNorm (w' i) *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
          (p.1 * p.2 - 1)) : ℂ × ℂ)) ⁻¹' {q}).Finite) ∧
    ∃ bc : C(↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
        fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))), X),
      ∀ (x : ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
          fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))) (i : Fin d),
        ((bc x : X) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' i) =
          ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i *
              (((x : Fin d → ℂ × ℂ) i).1 + ((x : Fin d → ℂ × ℂ) i).2),
            HeckeEigensystem.cNorm (w' i) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
              (((x : Fin d → ℂ × ℂ) i).1 * ((x : Fin d → ℂ × ℂ) i).2 - 1)) := by sorry
