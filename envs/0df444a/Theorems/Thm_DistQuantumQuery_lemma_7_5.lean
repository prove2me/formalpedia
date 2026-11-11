-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_7_5
-- name    : DistQuantumQuery.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:30.436997+00:00
-- url     : https://prove2.me/theorems/d51bb86c-dbdc-41a8-8e08-0f46a123ff9c
-- title:
--   Lemma 7.5 — properties of the lifting map $E^\uparrow_\Gamma$ and its adjoint channel $E^\downarrow_\Gamma$
-- statement:
--   Let $g:\Sigma_g\to\{0,1\}$ be a decision problem and $\Gamma\in L(\Sigma_g)$ real symmetric with $\|\Gamma\|\le1$ and $\Gamma\circ\Delta_g=\Gamma$. Then:
--
--   1. For every $X\in L(\{0,1\}^n)$, $E^\uparrow_\Gamma(X\circ I)=E^\uparrow_\Gamma(X)\circ I$. In particular $E^\uparrow_\Gamma(|\tilde x\rangle\langle\tilde x|)=I_{\mathbf g^{-1}(\tilde x)}$ for every $\tilde x\in\{0,1\}^n$, and $E^\uparrow_\Gamma(I)=I$.
--   2. The adjoint of $E^\uparrow_\Gamma$ is a quantum channel $E^\downarrow_\Gamma:L(\Sigma_g^n)\to L(\{0,1\}^n)$ given by $E^\downarrow_\Gamma(Y)=\mathbf G\big(Y\circ(\Gamma+I)^{\otimes n}\big)\mathbf G^\dagger$.
--   3. For every $Y\in L(\Sigma_g^n)$ and $X\in L(\{0,1\}^n)$, $E^\downarrow_\Gamma(Y)\circ X=E^\downarrow_\Gamma\big(Y\circ(\mathbf G^\dagger X\mathbf G)\big)$.
--   4. Let $\nu=(\nu_0+\nu_1)/2$ with $\nu_b$ a distribution supported on $g^{-1}(b)$, and $\mu$ a distribution on $\{0,1\}^n$. Then for every $Y\in L(\Sigma_g^n)$,
--   $$
--   E^\downarrow_\Gamma(Y\circ|\eta\rangle\langle\eta|)=2^n\,E^\downarrow_\Gamma\big(Y\circ|\nu\rangle\langle\nu|^{\otimes n}\big)\circ|\mu\rangle\langle\mu|,
--   $$
--   where $\eta=\mu\circ(\nu_0,\nu_1)$.
--
--   **Formalization Note** The adjoint is with respect to $\langle A,B\rangle=\mathrm{Tr}[A^\dagger B]$: $\langle E^\downarrow_\Gamma(Y),X\rangle=\langle Y,E^\uparrow_\Gamma(X)\rangle$. "Quantum channel" is written as completely positive and trace preserving.
--
--   Differences from the source:
--   - encoding: {0,1}^n and Σ_g^n with n blocks → ι → Bool and ι → Σ_g for a finite type ι of blocks; reason: relabelling the blocks; n = |ι|
--   - encoding: E↓_Γ completely positive → for every finite type R in Type and PSD Y on Σ_g^n × R, applying E↓_Γ blockwise gives a PSD matrix on {0,1}^n × R; reason: this is complete positivity (E↓_Γ ⊗ id_R positive for all finite R)
--   - encoding: I_{g⁻¹(x̃)} → the diagonal 0/1 matrix of {x ∈ Σ_g^n : g(x) = x̃}; reason: the same matrix
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 7.5, p.57; Definitions 7.2, 7.4, p.56

import Mathlib
import Definitions.Def_DistQuantumQuery_muMat
import Definitions.Def_DistQuantumQuery_traceNorm
import Definitions.Def_DistQuantumQuery_liftUp

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 7.5** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 7.5, p.57). Let `g : Σ_g → {0,1}`, and `Γ ∈ L(Σ_g)` real symmetric
with `‖Γ‖ ≤ 1` and `Γ ∘ Δ_g = Γ` (Definition 7.4). Then:
(i) `E↑_Γ(X ∘ I) = E↑_Γ(X) ∘ I` for every `X ∈ L({0,1}^n)`; in particular
`E↑_Γ(|x̃⟩⟨x̃|) = I_{g⁻¹(x̃)}` for every `x̃ ∈ {0,1}^n`, and `E↑_Γ(I) = I`.
(ii) The adjoint of `E↑_Γ` is a quantum channel `E↓_Γ : L(Σ_g^n) → L({0,1}^n)` given by
`E↓_Γ(Y) = **G**(Y ∘ (Γ + I)^{⊗n})**G**†`.
(iii) `E↓_Γ(Y) ∘ X = E↓_Γ(Y ∘ (**G**†X**G**))` for every `Y ∈ L(Σ_g^n)`, `X ∈ L({0,1}^n)`.
(iv) If `ν = (ν₀ + ν₁)/2` with `ν_b` a distribution supported on `g⁻¹(b)`, and `μ` is a distribution
on `{0,1}^n`, then `E↓_Γ(Y ∘ |η⟩⟨η|) = 2^n E↓_Γ(Y ∘ |ν⟩⟨ν|^{⊗n}) ∘ |μ⟩⟨μ|` for every `Y`, where
`η = μ ∘ (ν₀, ν₁)`.

**Formalization Note** `n = |ι|` blocks; `{0,1}^n` is `ι → Bool`, `Σ_g^n` is `ι → Σ_g`.
`I_{g⁻¹(x̃)}` is the diagonal 0/1 matrix of `{x : g(x) = x̃}`. Adjoint: `⟨E↓_Γ(Y), X⟩ = ⟨Y, E↑_Γ(X)⟩`
for the Hilbert–Schmidt inner product (§2.2, p.12). Quantum channel = completely positive and
trace preserving; complete positivity is positivity of `E↓_Γ ⊗ id_R` for every finite `R`
(block `(r, r')` of the input mapped by `E↓_Γ`). `η` on all of `Σ_g^n` is `compDistFull`. -/
theorem lemma_7_5 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Sg : Finset (κ → Bool)) (g : Sg → Bool) (Γ : Matrix Sg Sg ℂ) (hΓreal : ∀ x y, (Γ x y).im = 0) (hΓsymm : Γᵀ = Γ)
    (hΓnorm : opNorm Γ ≤ 1) (hΓg : Γ ⊙ disagree g = Γ) :
    -- (i)
    (∀ X : Matrix (ι → Bool) (ι → Bool) ℂ,
      liftUp g Γ (X ⊙ (1 : Matrix (ι → Bool) (ι → Bool) ℂ)) =
        liftUp g Γ X ⊙ (1 : Matrix (ι → Sg) (ι → Sg) ℂ)) ∧
    (∀ xt : ι → Bool, liftUp g Γ (Matrix.of fun a b => if a = xt ∧ b = xt then (1 : ℂ) else 0) =
      Matrix.diagonal fun x => if (fun i => g (x i)) = xt then (1 : ℂ) else 0) ∧
    liftUp g Γ (1 : Matrix (ι → Bool) (ι → Bool) ℂ) = 1 ∧
    -- (ii)
    (∀ (X : Matrix (ι → Bool) (ι → Bool) ℂ) (Y : Matrix (ι → Sg) (ι → Sg) ℂ),
      hsInner (liftDown g Γ Y) X = hsInner Y (liftUp g Γ X)) ∧
    (∀ (R : Type) [Fintype R] [DecidableEq R] (Y : Matrix ((ι → Sg) × R) ((ι → Sg) × R) ℂ),
      Y.PosSemidef →
        (Matrix.of fun (a : (ι → Bool) × R) (b : (ι → Bool) × R) =>
          liftDown g Γ (Matrix.of fun x y => Y (x, a.2) (y, b.2)) a.1 b.1).PosSemidef) ∧
    (∀ Y : Matrix (ι → Sg) (ι → Sg) ℂ, Matrix.trace (liftDown g Γ Y) = Matrix.trace Y) ∧
    -- (iii)
    (∀ (Y : Matrix (ι → Sg) (ι → Sg) ℂ) (X : Matrix (ι → Bool) (ι → Bool) ℂ),
      liftDown g Γ Y ⊙ X = liftDown g Γ (Y ⊙ ((liftG ι g)ᴴ * X * liftG ι g))) ∧
    -- (iv)
    (∀ (ν₀ ν₁ : Sg → ℝ), IsDist ν₀ → IsDist ν₁ → (∀ x, ν₀ x ≠ 0 → g x = false) →
      (∀ x, ν₁ x ≠ 0 → g x = true) → ∀ μ : (ι → Bool) → ℝ, IsDist μ →
      ∀ Y : Matrix (ι → Sg) (ι → Sg) ℂ,
        liftDown g Γ (Y ⊙ muMat (compDistFull g μ ν₀ ν₁)) =
          (((2 : ℂ) ^ Fintype.card ι) •
            liftDown g Γ (Y ⊙ tensorPow ι (muMat fun x => (ν₀ x + ν₁ x) / 2))) ⊙ muMat μ) := by sorry

end DistQuantumQuery
