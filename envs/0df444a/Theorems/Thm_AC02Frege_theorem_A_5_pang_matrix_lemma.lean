-- Prove2me | Theorems.Thm_AC02Frege_theorem_A_5_pang_matrix_lemma
-- name    : AC02Frege.theorem_A_5_pang_matrix_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:46:35.456667+00:00
-- url     : https://prove2.me/theorems/fb4e86b4-6ab7-4c7c-8a4e-a505cfd1b5c6
-- title:
--   Theorem A.5 — Pang's matrix lemma
-- statement:
--   Let $M_1,\dots,M_s$ be matrices over $\mathbb F_2$ of the same shape, and let $c$ be the rank of the stacked map $v\mapsto(M_1v,\dots,M_sv)$. Let $E=\mathbb F_2(\lambda_1,\dots,\lambda_s)$ be the field of rational functions in formal variables, and regard
--   $$
--   M(\lambda)=\sum_i\lambda_iM_i,\qquad M(\lambda^2)=\sum_i\lambda_i^2M_i
--   $$
--   as matrices over $E$. Suppose
--   $$
--   \ker_E M(\lambda)\subseteq\ker_E M(\lambda^2).\tag{48}
--   $$
--   Then $\mathrm{rank}_E M(\lambda)=c$, and $\mathbb E_{\epsilon\in\mathbb F_2^s}\,\mathrm{rank}_{\mathbb F_2}M(\epsilon)\ge c/2$. In particular some $\epsilon\in\mathbb F_2^s$ has $\mathrm{rank}\,M(\epsilon)\ge c/2$.
--
--   This is the algebraic core of the one-factor gain: a random $\mathbb F_2$-combination of the error matrices keeps half of their joint rank.
--
--   Differences from the source:
--   - encoding: E = F2(λ_1, …, λ_s); the expectation over ϵ ∈ F2^s → FractionRing (MvPolynomial (Fin s) (ZMod 2)) with λ_i the image of X i; the average of Matrix.rank over all 2^s points; reason: same field and same average
--   - encoding: the stacked map v ↦ (M_1 v, …, M_s v) → the matrix with rows indexed by Fin s × Fin p; reason: same linear map
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem A.5, (48), p.39

import Mathlib

namespace AC02Frege

open MvPolynomial Matrix

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Theorem A.5, (48), p.39 (Pang's matrix lemma [Pan26, Lemma 3.3]): let `M_1, …, M_s` be
matrices over `𝔽₂` of the same shape, let `c` be the rank of the stacked map
`v ↦ (M_1 v, …, M_s v)`, and suppose `ker_E M(λ) ⊆ ker_E M(λ²)` over
`E = 𝔽₂(λ_1, …, λ_s)`, where `M(λ) = Σ λ_i M_i` and `M(λ²) = Σ λ_i² M_i`. Then
`rank_E M(λ) = c` and `E_{ϵ ∈ 𝔽₂^s} rank_{𝔽₂} M(ϵ) ≥ c/2`; in particular some `ϵ` has
`rank M(ϵ) ≥ c/2`.

**Formalization Note** `E` is `FractionRing (MvPolynomial (Fin s) (ZMod 2))`, `λ_i` the image of
`X i`; the stacked map is the matrix with rows indexed by `Fin s × Fin p`; the expectation is
the average over all `2^s` points `ϵ : Fin s → ZMod 2`. -/
theorem theorem_A_5_pang_matrix_lemma {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let E := FractionRing (MvPolynomial (Fin s) (ZMod 2))
    let lam : Fin s → E := fun i => algebraMap (MvPolynomial (Fin s) (ZMod 2)) E (X i)
    let Mlam : Matrix (Fin p) (Fin q) E := ∑ i, lam i • (M i).map (algebraMap (ZMod 2) E)
    let Mlam2 : Matrix (Fin p) (Fin q) E := ∑ i, (lam i) ^ 2 • (M i).map (algebraMap (ZMod 2) E)
    let c : ℕ := (Matrix.of (fun (ik : Fin s × Fin p) (j : Fin q) => M ik.1 ik.2 j)).rank
    (∀ v : Fin q → E, Mlam *ᵥ v = 0 → Mlam2 *ᵥ v = 0) →
      Mlam.rank = c ∧
      (c : ℝ) / 2 ≤ (∑ ε : Fin s → ZMod 2, ((∑ i, ε i • M i).rank : ℝ)) / 2 ^ s ∧
      ∃ ε : Fin s → ZMod 2, (c : ℝ) / 2 ≤ ((∑ i, ε i • M i).rank : ℝ) := by sorry

end AC02Frege
