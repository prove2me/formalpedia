-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_lemma3_rounding
-- name    : ExpanderWalkDecode.Main.lemma3_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:46.408608+00:00
-- url     : https://prove2.me/theorems/5844121e-f80e-4f70-99cb-838374a4058d
-- title:
--   Lemma 3 (Step 3 Analysis) — the rounding routine outputs $\mathrm{LIST}(Y,\rho)$ with probability $\ge1/4$
-- statement:
--   Let $\{C_{n,\mathrm{base}}\}$ be a family of binary linear codes with a soft decoder of the form of Claim 12 (§4.3: one program, time $K_sn(\log_2(n+2))^{p_s}\lambda^{-c_s}\log(2+1/\delta)$, output $\{Z:\mathbb E_a[Z_aZ'_a]\ge2\lambda\}$ with probability $\ge1-\delta$). There are constants and one randomized program (the rounding routine of Figure 4) such that the following holds. Suppose the walk structure has $s,q\ge1$, a locally invertible outer graph with expansion $\le\lambda^2$, an inner Cayley graph with expansion $\le\lambda$, $0<\lambda\le1/4$, an embedding $\iota:[n]\hookrightarrow A$ with $|A|\le(1+\lambda^2)n$, and $C_{n,\mathrm{base}}$ has bias at most $\lambda^2/4$; let $Y\in\{\pm1\}$, $0<\rho\le1$ with
--   $$\frac{\rho^4}{16}\ge2\Big(\frac1{9\lambda^4}\Big)^{1+t/s}(19\lambda^2)^t,$$
--   $R\ge|\mathrm{WRW}^{\le t}_s(a)|$, and let $\{T_a\}$ be good parity operators. Then the program, given these inputs, halts within
--   $$K\Big(\frac{R+2}{\rho}\Big)^{c/\lambda^2}\big(N+|A|(d+1)^3+qsm+1\big)(\log_2(N+2))^p\lambda^{-c}$$
--   steps and outputs $\mathrm{LIST}(Y,\rho)$ with probability at least $1/4$.
--
--   This is Step 3 of the decoder; with $R,1/\rho=\mathrm{poly}(1/\varepsilon)$ the time is $\tilde O(N)(1/\varepsilon)^{O(1/\lambda^2)}$.
--
--   Differences from the source:
--   - generalization: the construction's graphs and base code → any walk structure and base family with the listed properties (expansions λ², λ, local invertibility, bias λ²/4, a Claim-12 soft decoder); reason: these are the properties the proof uses; specializes
--   - reading: Õ(N)·(1/ε)^{O(1/λ²)} → K((R+2)/ρ)^{c/λ²}(N + |A|(d+1)³ + qsm + 1)(log₂(N+2))^p λ^{-c}; reason: for a general walk structure R, 1/ρ and the input size are the parameters the paper bounds by poly(1/ε) and N
--   - reading: D_round (the algorithm in Figure 4), with the construction's |A| = n(1+o_n(1)) → there is a program; |A| ≤ (1+λ²)n among the hypotheses; reason: Figure 4 calls the existential decoder of Claim 12; the size condition makes the padded lists short, as the runtime analysis assumes
--   - encoding: LIST(Y, ρ) as amplified codewords → the base codewords, output as sign vectors; reason: the amplification is injective on the base code under these hypotheses; same list
--   - generalization: a received word on the support set of wide replacement walks → an arbitrary received sign word on the full latent-coordinate space; reason: a source word pulls back along the walk map; all copies of a support coordinate then have the same received sign. The extension keeps the latent sampling law and charges every coordinate
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 16 (PDF p. 19), §4.3, Lemma 3

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Lemma 3 (Step 3 Analysis) (§4.3, p. 16): for a base-code family with bias at most `λ²/4`
whose soft decoder (Claim 12, form of §4.3) runs in time `Õ(n) poly(1/λ) log(1/δ)`, there is one
randomized program (the rounding routine of Figure 4) that, given the walk structure (with
`λ_A ≤ λ²`, `λ_B ≤ λ`, `A` locally invertible, `0 < λ ≤ 1/4`, `|A| ≤ (1 + λ²) n`), `Y`, `ρ ∈ (0, 1]`
with `ρ⁴/16 ≥ 2 (1/(9λ⁴))^{1+t/s} (19λ²)^t`, `R ≥ |WRW^{≤t}_s(a)|` and good parity operators,
outputs `LIST(Y, ρ)` with probability at least `1/4` in time `Õ(N) (R/ρ)^{O(1/λ²)}`. -/
theorem lemma3_rounding :
    ∀ (Cb : ∀ n : ℕ, BinaryLinearCode n) (Psoft : Program) (Ks cs : ℝ) (ps : ℕ), Admissible Psoft →
      ∃ (K c : ℝ) (p : ℕ) (P : Program), Admissible P ∧
        ∀ (nA m s q t : ℕ) (G : RotGraph (Fin nA) (Fin m → ZMod 2)) (u : Fin q → Inner m s) (R d n : ℕ)
          (ι : Fin n ↪ Fin nA) (Y : Latent (Fin nA) m s q t → ℝ) (ρ lam : ℝ)
          (T : Fin nA → Matrix (Fin d) (Fin d) ℝ),
          0 < s → 0 < q → G.LocallyInvertible → G.IsExpander (lam ^ 2) →
          (cayley u).IsExpander lam → 0 < lam → lam ≤ 1 / 4 → (nA : ℝ) ≤ (1 + lam ^ 2) * n →
          0 < ρ → ρ ≤ 1 → ampThreshold lam s t ≤ ρ ^ 4 / 16 → HasBias (Cb n) (lam ^ 2 / 4) →
          (∀ a, (fromW G u t a).card ≤ R) → (∀ z, Y z = 1 ∨ Y z = -1) →
          (∀ (δ : ℝ) (Z' : Fin nA → ℝ), 0 < δ → (∀ a, Z' a ∈ Set.Icc (-1 : ℝ) 1) →
            RunsWithin Psoft (softInput ι δ lam Z')
              (Ks * n * Real.logb 2 ((n : ℝ) + 2) ^ ps * (1 / lam) ^ cs * Real.log (2 + 1 / δ))
              (fun out => EncodesWordList out (softListA (Cb n) ι lam Z')) (1 - δ)) →
          GoodParityOps G u t ι (Cb n) Y ρ R T →
          RunsWithin P (structInput G u t [(R : ℤ), (d : ℤ), (n : ℤ)] (embBank ι) [ρ, lam]
              (latentBank Y) (opsList T))
            (K * (((R : ℝ) + 2) / ρ) ^ (c / lam ^ 2)
              * ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + nA * ((d : ℝ) + 1) ^ 3 + q * s * m + 1)
              * Real.logb 2 ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + 2) ^ p * (1 / lam) ^ c)
            (fun out => EncodesWordList out (listSet G u t ι (Cb n) Y ρ)) (1 / 4) := by sorry

end ExpanderWalkDecode.Main
