-- Prove2me | Theorems.Thm_EntangledPIR_lemma_3_5
-- name    : EntangledPIR.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:54.789227+00:00
-- url     : https://prove2.me/theorems/16e6440b-3daf-4025-a250-7ae6daad607b
-- title:
--   Lemma 3.5 — blocks within the privacy threshold
-- statement:
--   Suppose that (3.1) holds, and fix $t\in[\ell]^k$ and a register $\mathsf R$.
--
--   1. For all $S,S'\subseteq[k]$, the operator $P_{S'}|J\rangle\langle J|_tP_S$ depends on $J\in(\{0,1\}^d)^k$ only through the coordinates $J_i$ with $i\in S\cup S'$.
--   2. Let $\lambda\ge0$, and suppose that the sharing has privacy threshold $\lambda$. Then $R_x(|t\rangle\langle t|_{\mathsf T}\otimes P_S\Theta P_{S'})$ is the same for all $x$, for every operator $\Theta$ on $\mathsf{RB}$ and all $S,S'$ with $|S\cup S'|\le\lambda$. In particular, $R_x(|t\rangle\langle t|_{\mathsf T}\otimes\Theta)$ is the same for all $x$ for every $(s,s')$-block $\Theta$ with $s+s'\le\lambda$.
--
--   This is the step where the privacy threshold enters the cut-and-choose bound.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: the copy $\mathsf B_{i,j}$ contains $\mathsf P'_{i,j}$ → $\mathsf B_{i,j}=\mathsf P'_{i,j}\otimes\mathsf E_{i,j}$ for a finite $\mathsf E_{i,j}$; reason: a register containing a register is a tensor product
--   - encoding: an $(s,s')$-block $\Theta=E_s\Theta E_{s'}$ on $\mathsf{RB}$ → `Θ = onB (Ets Pi t s) * Θ * onB (Ets Pi t s')`; reason: the definition on p.14, with $E_s$ acting on $\mathsf B$ inside $\mathsf{RB}$
--   - encoding: the secrets form a finite set (p.12); the distributions $\mu_x$ → `[Fintype X]`, and `IsShareDistribution mu` with `mu x y : ℝ`; reason: Lean convention
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 3.5, p.15

import Definitions.Def_EntangledPIR_CutChoose

open Matrix

namespace EntangledPIR

/-- **Lemma 3.5 (Blocks within the Privacy Threshold)**, Mantri, manuscript (Nov. 2026), p.15. Suppose that
(3.1) holds, and fix `t ∈ [ℓ]^k` and a register `R`. (i) For all `S, S′ ⊆ [k]`, the operator
`P_{S′} |J⟩⟨J|_t P_S` depends on `J` only through the coordinates `J_i` with `i ∈ S ∪ S′`. (ii) If the sharing has
privacy threshold `λ`, then `R_x(|t⟩⟨t|_T ⊗ P_S Θ P_{S′})` is the same for all `x`, for every operator `Θ` on `RB`
and all `S, S′` with `|S ∪ S′| ≤ λ`. In particular, `R_x(|t⟩⟨t|_T ⊗ Θ)` is the same for all `x` for every
`(s, s′)`-block `Θ = E_s Θ E_{s′}` with `s + s′ ≤ λ`. -/
theorem lemma_3_5 {k ℓ d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hℓ : 2 ≤ ℓ) {E : Fin k × Fin ℓ → Type}
    [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]
    (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (hPi : IsTestFamily Pi)
    (t : Positions k ℓ) (R : Type) [Fintype R] [DecidableEq R] :
    (∀ (S S' : Finset (Fin k)) (J J' : ShareVec k d), (∀ i ∈ S ∪ S', J i = J' i) →
      PtS Pi t S' * JProj t J * PtS Pi t S = PtS Pi t S' * JProj t J' * PtS Pi t S) ∧
    (∀ (lam : ℕ) {X : Type} [Fintype X] (mu : X → ShareVec k d → ℝ), IsShareDistribution mu →
      HasPrivacyThreshold mu lam →
      (∀ (Θ : Matrix (R × AllB d E) (R × AllB d E) ℂ) (S S' : Finset (Fin k)),
        (S ∪ S').card ≤ lam → ∀ x x' : X,
          Rmap (R := R) (mu x) (classicalBlock t (onB (PtS Pi t S) * Θ * onB (PtS Pi t S'))) =
            Rmap (R := R) (mu x') (classicalBlock t (onB (PtS Pi t S) * Θ * onB (PtS Pi t S')))) ∧
      (∀ (Θ : Matrix (R × AllB d E) (R × AllB d E) ℂ) (s s' : ℕ), s + s' ≤ lam →
        Θ = onB (Ets Pi t s) * Θ * onB (Ets Pi t s') → ∀ x x' : X,
          Rmap (R := R) (mu x) (classicalBlock t Θ) = Rmap (R := R) (mu x') (classicalBlock t Θ))) := by sorry

end EntangledPIR
