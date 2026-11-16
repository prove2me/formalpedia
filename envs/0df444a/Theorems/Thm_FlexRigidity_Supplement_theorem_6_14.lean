-- Prove2me | Theorems.Thm_FlexRigidity_Supplement_theorem_6_14
-- name    : FlexRigidity.Supplement.theorem_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:19:04.549256+00:00
-- url     : https://prove2.me/theorems/e4dde00e-e248-413e-90be-5bb6b6e290e2
-- title:
--   Theorem 6.14 — sequential blind randomness expansion from the Magic Square game
-- statement:
--   For every $\gamma\in(0,1)$ there is $\vartheta_0>0$ such that for every $\vartheta\in(0,\vartheta_0)$ there is a tolerance $\varepsilon_{\mathrm{tol}}\in(0,\tfrac{1-\gamma}2]$ for which Protocol 6, with $m=\lfloor(1-\gamma)n/2\rfloor$, satisfies the following.
--
--   1. For every $n\ge4/(1-\gamma)$, every device implementation and Bob strategy allowed by Postulate Set 5.4 and every initial state,
--   $$p_{\mathrm{Acc}}\,p_{\mathrm{guess}}(K_E\mid Z)_{\rho^{\mathrm{real}}_{|\mathrm{Acc}}}\le2^{-\vartheta n},\qquad Z=M^B_{n+1}R\,XYBCT, \tag{82}$$
--   and, for every output length $\ell$ and every independent uniform seed selecting a two-universal hash $\{0,1\}^m\to\{0,1\}^\ell$, the secrecy error of $L=h_D(K_E)$ in (80) satisfies
--   $$\varepsilon_{\mathrm{sec}}\le2^{\ell/2-\vartheta n/2}.$$
--   2. For every honest noise level $\delta_{\mathrm{hon}}\in[0,\tfrac12]$ with $\delta_{\mathrm{hon}}<\varepsilon_{\mathrm{tol}}/\gamma$, the honest implementation (depolarizing noise $2\delta_{\mathrm{hon}}$ on two EPR pairs, perfect Magic Square measurements) has acceptance probability $p_{\mathrm{Acc}}\ge1-\mathrm{negl}(n)$.
--
--   Bob, who chooses the devices and keeps his complete memory and the public transcript, cannot predict the generated key bits, so Alice obtains $\Omega(\vartheta n)$ bits that are random even to the adversary supplying her device.
--
--   **Formalization Note** (82) is stated for every guessing measurement on $Z$ (its maximum is $p_{\mathrm{Acc}}p_{\mathrm{guess}}$); "every allowed attack" in the secrecy clause is every implementation, initial state and two-universal family; $\mathrm{negl}$ is the published `PPADSIS.SubexpSIS.Negligible` applied to $1-p_{\mathrm{Acc}}$.
--
--   Differences from the source:
--   - encoding: pAcc · pguess(K_E | Z) of the normalized accepted state → for every guessing measurement reading Z's classical part (c, x, y, b, t) and a POVM on R M^B_{n+1}, Σ_k Tr[(|k⟩⟨k| ⊗ G_k) ρ_{K_E Z ∧ Acc}] ≤ 2^{−ϑn}; reason: pAcc·pguess(·)_{ρ|Acc} is the maximum of this sum (both 0 when pAcc = 0), and since ρ is block diagonal in Z's classical registers, block-diagonal POVMs attain the maximum
--   - encoding: secrecy error εsec of (80) for the two-universal extractor → breSecrecy, the trace distance written as the sum over the classical blocks (L, D, (u, x, y, b, c, t)), for every ℓ, every finite nonempty seed set and every two-universal family; reason: the operator is block diagonal in classical registers, so the trace norm is the sum of blockwise trace norms; Rin ∪ Cpub = X Y U T D B C
--   - reading: the parameter choice in the proof specifies a tolerance εtol = εtol(γ, ϑ) > 0 → ∃ εtol ∈ (0, (1−γ)/2] after ϑ; reason: Protocol 6 takes εtol from Protocol 2, whose range is (0,(1−γ)/2]; the proof chooses εtol in that interval ((84), p. 72)
--   - encoding: Postulate Set 5.4 devices for Protocol 6, where Bob receives y_i and answers b_i in every round → BRImpl with Alice's instruments E^{A,x,a}_i and Bob's instruments E^{B,y,b}_i in every round, product action, arbitrary finite memories; reason: during Protocol 6 Bob learns only y_i (p. 70); the published DIImpl's test/generation split does not apply
--   - generalization: honest implementation with the fixed perfect Magic Square strategy of Fact 6.11 → every perfect strategy on two EPR pairs with rank-one projective measurements; reason: the source's fixed strategy is one of them
--   - reading: honest depolarizing noise 2δhon, δhon < εtol/γ → δhon ∈ [0, ½] with δhon < εtol/γ; reason: 2δhon ≤ 1 is the range of a depolarizing weight
--   - reading: pAcc ≥ 1 − negl(n) → n ↦ 1 − pAcc(n) is negligible (PPADSIS.SubexpSIS.Negligible); reason: the standard meaning of negl(n); the paper does not define it
--   - encoding: honest rounds with a fresh noisy copy of the two EPR pairs → explicit product law over rounds (brePAccHonest); reason: honest rounds are independent and identical (p. 60)
--   - encoding: Z = M^B_{n+1} X Y B C T and M^B_fin = M^B_{n+1} → Bob's quantum register is R M^B_{n+1}, with R the register of the initial state ρ⁰ of every dimension r; reason: in Definition 6.4 Bob supplies the joint initial state of the device and his own memory, so R is part of his memory; r = 1 is the source's case and any R can be absorbed into M^B_1
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Theorem 6.14, eq. (82), p. 72

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_FlexRigidity_Supplement_Basics
import Definitions.Def_FlexRigidity_Supplement_MagicSquare
import Definitions.Def_FlexRigidity_Supplement_BRE

set_option autoImplicit false

open QAlgorithms.Papers.Independent.Dependency50.P35 (Density POVM)

noncomputable section

namespace FlexRigidity.Supplement

/-- **Theorem 6.14 (Sequential blind randomness expansion under depolarizing noise)**
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 72).
Under Postulate Set 5.4, for every `γ ∈ (0, 1)` there is a constant `ϑ₀(γ) > 0` such that, for
every `0 < ϑ < ϑ₀(γ)`, the parameter choice in the proof specifies a tolerance
`ε_tol = ε_tol(γ, ϑ) > 0`. Protocol 6 then satisfies, for every integer `n ≥ 4/(1−γ)` and every
allowed implementation and attack, `p_Acc p_guess(K_E | Z)_{ρ^real_{|Acc}} ≤ 2^{−ϑn}` (82). With
an independent uniform seed selecting a two-universal hash `{0,1}^m → {0,1}^ℓ`, the secrecy error
satisfies `ε_sec ≤ 2^{ℓ/2 − ϑn/2}`. For `δ_hon < ε_tol/γ`, the honest acceptance probability is
`p_Acc ≥ 1 − negl(n)`.

**Formalization Note** `ε_tol ∈ (0, (1−γ)/2]` (Protocol 2's range). (82) is stated for every
guessing measurement on `Z = M^B_{n+1} R X Y B C T` that may read `Z`'s classical part
(`breGuess`); `p_Acc · p_guess` of the accepted state is the maximum of `breGuess` (both are `0`
when `p_Acc = 0`). The secrecy clause is for every output length `ℓ`, every finite seed set and
every two-universal family, as the distance `breSecrecy` of (80). The honest clause is for every
`δ_hon ∈ [0, ½]` with `δ_hon < ε_tol/γ` and every perfect rank-one Magic Square strategy on two EPR
pairs (the honest measurements, p. 60); `negl` is `PPADSIS.SubexpSIS.Negligible` applied to
`1 − p_Acc`. -/
theorem theorem_6_14 :
    ∀ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ ϑ0 : ℝ, 0 < ϑ0 ∧
      ∀ ϑ ∈ Set.Ioo 0 ϑ0, ∃ εtol ∈ Set.Ioc (0 : ℝ) ((1 - γ) / 2),
        (∀ n : ℕ, 4 / (1 - γ) ≤ (n : ℝ) →
          ∀ I : BRImpl (Fin 3) (Fin 3) MSRow MSCol, I.IsAllowed n →
          ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
              (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
            (∀ G : (Fin n → BRZCl) → (Fin (mLen γ n) → Bool) →
                Matrix (Fin r × Fin (I.dB n)) (Fin r × Fin (I.dB n)) ℂ,
              (∀ z, POVM (G z)) → breGuess γ εtol n I ρ0 G ≤ (2 : ℝ) ^ (-(ϑ * n))) ∧
            ∀ (ℓ : ℕ) (D : Type) [Fintype D] [Nonempty D]
              (hash : D → (Fin (mLen γ n) → Bool) → (Fin ℓ → Bool)),
              IsTwoUniversal ℓ hash →
                breSecrecy γ εtol n I ρ0 ℓ hash ≤ (2 : ℝ) ^ ((ℓ : ℝ) / 2 - ϑ * n / 2)) ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → δ < εtol / γ →
        ∀ (T : Fin 3 → MSRow → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
          (N : Fin 3 → MSCol → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
          IsPerfectMSStrategy T N →
            PPADSIS.SubexpSIS.Negligible (fun n => 1 - brePAccHonest δ γ εtol n T N) := by sorry

end FlexRigidity.Supplement
