-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_exists_summable_majorant_of_lattice_vanishing
-- name    : EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5fd75be1-d153-5ccb-90cd-600bd234dda5
-- title:
--   Summable majorant for Eisenstein coefficient pieces
-- statement:
--   Let $F$ be a number field, $n$ a natural number and $R$ a real number. Data: continuous functions $C_j:\mathbb{C}\to\mathbb{C}$ for $j\in\mathrm{Fin}\,n$; a function $K$ on the nonzero elements $\xi$ of $F$ with $\|K(\xi)\|\le K_0$ for all $\xi$; functions $J^{\mathrm{r}}_{j,i}(s,t)$ indexed by $j$ and by the real infinite places $i$ of $F$, each satisfying, for some constants $C_1,c_1>0$ and some $N_1\in\mathbb{N}$ depending on $(j,i)$, the bound $\|J^{\mathrm{r}}_{j,i}(s,t)\|\le C_1\max(1,|t|^{-N_1})e^{-c_1|t|}$ whenever $\|s\|\le R$ and $t\ne 0$; functions $J^{\mathrm{c}}_{j,w}(s,\zeta)$ indexed by $j$ and by the complex infinite places $w$, with the analogous bound $C_1\max(1,\|\zeta\|^{-N_1})e^{-c_1\|\zeta\|}$ for $\|s\|\le R$, $\zeta\ne 0$; nonvanishing twists $\theta^{\mathrm{r}}_i\in\mathbb{R}$, $\theta^{\mathrm{c}}_w\in\mathbb{C}$ and $\alpha_1(i)\in\mathbb{R}$, $\alpha_2(w)\in\mathbb{C}$; a map $q$ from nonzero elements of $F$ to the mixed space of $F$ whose real coordinate at $i$ is the $i$-th coordinate of the mixed embedding of $\xi$ times $\alpha_1(i)$ and whose complex coordinate at $w$ is the $w$-th coordinate times $\alpha_2(w)$; a fractional ideal $I$ of $F$; and functions $\Phi_j(\xi,s)$ vanishing whenever $\xi\notin I$ and satisfying $\|\Phi_j(\xi,s)\|\le P\,\max\bigl(1,|N_{F/\mathbb{Q}}(\xi)|\bigr)^{k}$ for $\xi\in I$ and $\|s\|\le R$. Then there exists a real-valued family $M$ on the nonzero elements of $F$ which is summable and such that for every such $\xi$ and every $s$ with $\|s\|\le R$, the norm of $\sum_j C_j(s)K(\xi)\prod_i J^{\mathrm{r}}_{j,i}\bigl(s,-\theta^{\mathrm{r}}_i (q\xi)_i\bigr)\prod_w J^{\mathrm{c}}_{j,w}\bigl(s,-\theta^{\mathrm{c}}_w (q\xi)_w\bigr)\Phi_j(\xi,s)$ is at most $M(\xi)$.
--
--   This is the analytic convergence input for the general Eisenstein construction: it produces a single summable majorant, uniform on the disc $\|s\|\le R$, for a family of coefficients assembled from archimedean factors with exponential decay and at most polynomial singularities, a bounded factor, and a factor supported on a fractional ideal with polynomial growth in the absolute norm. It is used in the construction of entire partial Euler products matching Whittaker coefficients together with a summable majorant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_exists_summable_majorant_of_lattice_vanishing.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

open scoped Classical in

theorem EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing
    (F : Type) [Field F] [NumberField F] (n : ℕ) (R : ℝ)
    (C : Fin n → ℂ → ℂ) (hC : ∀ j, Continuous (C j))
    (Kf : {ξ : F // ξ ≠ 0} → ℂ) (K₀ : ℝ) (hK : ∀ ξ, ‖Kf ξ‖ ≤ K₀)
    (Jr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
    (hJr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}), ∃ C₁ c₁ : ℝ, ∃ N₁ : ℕ,
      0 < C₁ ∧ 0 < c₁ ∧ ∀ (s : ℂ) (t : ℝ), ‖s‖ ≤ R → t ≠ 0 →
        ‖Jr j i s t‖ ≤ C₁ * max 1 (|t| ^ (-(N₁ : ℝ))) * Real.exp (-c₁ * |t|))
    (Jc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
    (hJc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), ∃ C₁ c₁ : ℝ, ∃ N₁ : ℕ,
      0 < C₁ ∧ 0 < c₁ ∧ ∀ (s ζ : ℂ), ‖s‖ ≤ R → ζ ≠ 0 →
        ‖Jc j w s ζ‖ ≤ C₁ * max 1 (‖ζ‖ ^ (-(N₁ : ℝ))) * Real.exp (-c₁ * ‖ζ‖))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (q : {ξ : F // ξ ≠ 0} → mixedEmbedding.mixedSpace F)
    (α₁ : {w : InfinitePlace F // w.IsReal} → ℝ) (hα₁ : ∀ i, α₁ i ≠ 0)
    (α₂ : {w : InfinitePlace F // w.IsComplex} → ℂ) (hα₂ : ∀ w, α₂ w ≠ 0)
    (hq₁ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (i : {w : InfinitePlace F // w.IsReal}),
      (q ξ).1 i = (mixedEmbedding F ξ.1).1 i * α₁ i)
    (hq₂ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (w : {w : InfinitePlace F // w.IsComplex}),
      (q ξ).2 w = (mixedEmbedding F ξ.1).2 w * α₂ w)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Φ : Fin n → {ξ : F // ξ ≠ 0} → ℂ → ℂ)
    (hΦ0 : ∀ (j : Fin n) (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ξ.1 ∉ I → Φ j ξ s = 0)
    (P : ℝ) (k : ℕ) (hΦ : ∀ (j : Fin n) (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ξ.1 ∈ I →
      ‖Φ j ξ s‖ ≤ P * (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k) :
    ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧ ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R →
      ‖∑ j : Fin n, C j s * Kf ξ
        * (∏ i : {w : InfinitePlace F // w.IsReal}, Jr j i s (-(θr i * (q ξ).1 i)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex}, Jc j w s (-(θc w * (q ξ).2 w)))
        * Φ j ξ s‖ ≤ M ξ := by sorry
