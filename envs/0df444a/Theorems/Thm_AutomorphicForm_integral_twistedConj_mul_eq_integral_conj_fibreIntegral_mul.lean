-- Prove2me | Theorems.Thm_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
-- name    : AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/4545f756-2226-57e8-87d4-abb1f38b8541
-- title:
--   Shear change of variables for twisted orbital integrals
-- statement:
--   Let $G$ be a group with a measurable structure for which multiplication (as a function of two variables) and inversion are measurable, and let $\mu$ be a $\sigma$-finite left-invariant measure on $G$. Fix $n$ and $\delta : \mathrm{Fin}(n+1)\to G$, and let $\mathrm{twc}$ be the twisted conjugation $(\mathrm{twc}\,x)_j = x_j^{-1}\delta_j x_{j+1}$ (indices read cyclically in $\mathrm{Fin}(n+1)$), let $T$ be a subgroup of $G^{\mathrm{Fin}(n+1)}$ whose elements are exactly the $t$ with $t_j^{-1}\delta_j t_{j+1}=\delta_j$ for all $j$, and let $y_0,\gamma\in G$ satisfy $\gamma=y_0^{-1}(\delta_0\cdots\delta_n)y_0$. Let $\Phi:G^{\mathrm{Fin}(n+1)}\to\mathbb{C}$ be measurable and bounded in norm, and let $f,f_1:G\to\mathbb{C}$ be the fibre integrals $f(h)=\int \Phi(c_0,\dots,c_{n-1},(c_0\cdots c_{n-1})^{-1}h)\,d\mu^{n}(c)$ and $f_1(h)=\int \|\Phi(c_0,\dots,c_{n-1},(c_0\cdots c_{n-1})^{-1}h)\|\,d\mu^{n}(c)$. Assume $T$ and the centraliser of $\{\gamma\}$ in $G$ carry measures $\tau'$ and $\tau$ such that $t\mapsto y_0^{-1}t_0y_0$ and the inclusion of the centraliser into $G$ are measurable and push $\tau'$ and $\tau$ forward to the same measure on $G$. Assume further two hypotheses of independence of the cut-off: for every measurable $F$ on $G^{\mathrm{Fin}(n+1)}$ invariant under left translation by $T$, and any two non-negative measurable weights each of whose $\tau'$-integral along the $T$-orbit of $x$ equals $1$ whenever $F(x)\neq0$, the integrals of $F$ against the two weights over $\mu^{n+1}$ agree; and the analogous statement on $G$ for functions invariant under left translation by the centraliser of $\gamma$, with $\tau$. Finally let $W_0\ge 0$ be measurable on $G^{\mathrm{Fin}(n+1)}$ with $\int_T W_0(t\cdot x)\,d\tau'=1$ whenever $\Phi(\mathrm{twc}\,x)\neq0$, let $w_0\ge0$ be measurable on $G$ with $\int w_0(sh)\,d\tau=1$ over the centraliser whenever $f(h^{-1}\gamma h)\neq0$, and assume there exist a non-negative measurable $\mu$-integrable $w_1$ satisfying the same normalisation at the points where $f_1(h^{-1}\gamma h)\neq0$, and a non-negative measurable $\mu^{n}$-integrable $\beta$ on $G^{\mathrm{Fin}\,n}$ with $\beta(c)=1$ whenever $\Phi(c_0,\dots,c_{n-1},h)\neq0$ for some $h$. Then $\int \Phi(\mathrm{twc}\,x)W_0(x)\,d\mu^{n+1}(x)=\int f(h^{-1}\gamma h)\,w_0(h)\,d\mu(h)$.
--
--   This is the local shear computation comparing a twisted orbital integral for the cyclic shift on $G^{n+1}$ with the ordinary orbital integral, at the norm $\delta_0\cdots\delta_n$, of the fibre integral of $\Phi$ over the first $n$ shear coordinates; the weights $W_0$ and $w_0$ play the role of sections trivialising the respective orbit measures. It is used in the construction of matching local and archimedean test data attached to algebra homomorphisms of Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] {n : ℕ} (δ : Fin (n + 1) → G)
    (twc : (Fin (n + 1) → G) → Fin (n + 1) → G)
    (htwc : ∀ x j, twc x j = (x j)⁻¹ * δ j * x (j + 1))
    (T : Subgroup (Fin (n + 1) → G)) (hT : ∀ t, t ∈ T ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j)
    (y₀ γ : G) (hγ : γ = y₀⁻¹ * (List.ofFn δ).prod * y₀)
    (Φ : (Fin (n + 1) → G) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (f f₁ : G → ℂ)
    (hf : ∀ h, f h =
      ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ))
    (hf₁ : ∀ h, f₁ h =
      ∫ c : Fin n → G, (‖Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))‖ : ℂ) ∂(Measure.pi fun _ => μ))
    [MeasurableSpace T] (τ' : Measure T)
    (hmeas : Measurable fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G)))
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (hτ : Measure.map (fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ)
    (huniqT : ∀ F : (Fin (n + 1) → G) → ℂ, Measurable F →
      (∀ (t : T) (x : Fin (n + 1) → G), F ((t : Fin (n + 1) → G) * x) = F x) →
      ∀ w w' : (Fin (n + 1) → G) → ℝ, (∀ x, 0 ≤ w x) → (∀ x, 0 ≤ w' x) →
        Measurable w → Measurable w' →
        (∀ x, F x ≠ 0 → ∫ t : T, w ((t : Fin (n + 1) → G) * x) ∂τ' = 1) →
        (∀ x, F x ≠ 0 → ∫ t : T, w' ((t : Fin (n + 1) → G) * x) ∂τ' = 1) →
        ∫ x, F x * (w x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
          ∫ x, F x * (w' x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ))
    (huniqG : ∀ F : G → ℂ, Measurable F →
      (∀ (s : Subgroup.centralizer ({γ} : Set G)) (h : G), F ((s : G) * h) = F h) →
      ∀ w w' : G → ℝ, (∀ h, 0 ≤ w h) → (∀ h, 0 ≤ w' h) → Measurable w → Measurable w' →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w ((s : G) * h) ∂τ = 1) →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w' ((s : G) * h) ∂τ = 1) →
        ∫ h, F h * (w h : ℂ) ∂μ = ∫ h, F h * (w' h : ℂ) ∂μ)
    (W₀ : (Fin (n + 1) → G) → ℝ) (hW₀ : ∀ x, 0 ≤ W₀ x) (hW₀m : Measurable W₀)
    (hW₀1 : ∀ x, Φ (twc x) ≠ 0 → ∫ t : T, W₀ ((t : Fin (n + 1) → G) * x) ∂τ' = 1)
    (w₀ : G → ℝ) (hw₀ : ∀ h, 0 ≤ w₀ h) (hw₀m : Measurable w₀)
    (hw₀1 : ∀ h, f (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₀ ((s : G) * h) ∂τ = 1)
    (hw₁ : ∃ w₁ : G → ℝ, (∀ h, 0 ≤ w₁ h) ∧ Measurable w₁ ∧ Integrable w₁ μ ∧
      ∀ h, f₁ (h⁻¹ * γ * h) ≠ 0 →
        ∫ s : Subgroup.centralizer ({γ} : Set G), w₁ ((s : G) * h) ∂τ = 1)
    (hβ : ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∫ x, Φ (twc x) * (W₀ x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ h, f (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ := by sorry
