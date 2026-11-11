-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_lemma1_vector_recovery
-- name    : ExpanderWalkDecode.Main.lemma1_vector_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:56.953765+00:00
-- url     : https://prove2.me/theorems/a542e2e0-4fe8-42ef-9d87-59db2aca510e
-- title:
--   Lemma 1 (Step 1 Analysis) — good vectors with probability $\ge1/2$ in time $\tilde O(N)\,\mathrm{poly}$
-- statement:
--   There are absolute constants $C>0$, $K$, $c$, $p$ and one randomized program (the vector-recovery routine of Figure 2) with the following property. Given the walk structure, $Y\in\{\pm1\}$ on the $N$ code coordinates, $0<\rho\le1$ and $R\ge|\mathrm{WRW}^{\le t}_s(a)|$ for all $a$, it halts within
--   $$K\,(N+|A|+qsm+1)\,(\log_2(N+2))^p\Big(\frac{(R+1)(t+1)}{\rho}\Big)^{c}$$
--   steps and, for every base code $C_{\mathrm{base}}$ and embedding $\iota$, outputs with probability at least $1/2$ good vectors (Definition 2, for $\mathrm{LIST}(Y,\rho)$ of that code) in dimension $D=1+M\Delta$, where $\alpha=10240R^2(t+1)^3/\rho^8$, $M=\lceil144(4+64\alpha)/\rho^4\rceil$ and $\Delta=\lceil C(12+64\alpha)^2\rho^{-4}\log(2+NR)\rceil$.
--
--   This is Step 1 of the decoder.
--
--   Differences from the source:
--   - generalization: the paper's walk structure (graphs of Proposition 3, base code of Proposition 1) → any outer graph with ports F_2^m, any inner Cayley graph on (F_2^m)^s, any t, any base code and embedding; reason: the statement uses no expansion property; specializes to the paper's structure
--   - reading: Õ(N)·poly(1/ε) → K(N + |A| + qsm + 1)·(d+1)·(log₂(N+2))^p·((R+1)(t+1)/ρ)^c with absolute constants, N the number of code coordinates; reason: for a general walk structure the input size and R, t, 1/ρ are the parameters that the paper bounds by N and poly(1/ε); the factor d+1 charges input vector coordinates, and the source dimension D is poly(1/ε) times a polylogarithm in N
--   - reading: E_{a∼A} E_{⃗a,⃗a′∼WRW^{≤t}_s(a)} in G(P) → ⃗a, ⃗a′ drawn uniformly from the set WRW^{≤t}_s(a); reason: the source gives no other law on walks of mixed lengths; Claim 11's proof bounds sums over WRW^{≤t}_s(a) by R times this average
--   - reading: D_vec (the algorithm in Figure 2) → there is a program; reason: Figure 2 calls the existential routine of Claim 7, so it is not a fixed program; the conclusion is the one the source proves for it
--   - reading: D = 1 + MΔ, Δ = O((12+64α)² log(N)/ρ⁴) → D = 1 + M⌈C(12+64α)²ρ^{-4} log(2+NR)⌉; reason: as in Claim 7
--   - generalization: a received word on the support set of wide replacement walks → an arbitrary received sign word on the full latent-coordinate space; reason: a source word pulls back along the walk map; all copies of a support coordinate then have the same received sign. The extension keeps the latent sampling law and charges every coordinate
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 12 (PDF p. 15), §4.1, Lemma 1

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Lemma 1 (Step 1 Analysis) (§4.1, p. 12): there are absolute constants and one randomized
program (the vector-recovery routine of Figure 2) that, run on the walk structure,
`Y ∈ {±1}^{WRW^t_s}`, `0 < ρ ≤ 1` and `R ≥ |WRW^{≤t}_s(a)|`, runs in time
`Õ(N) poly(R, t, 1/ρ)` and with probability at least `1/2` outputs good vectors (Definition 2) in
dimension `D = 1 + MΔ`, with `α, M, Δ` as in §4.1. -/
theorem lemma1_vector_recovery :
    ∃ (C K c : ℝ) (p : ℕ) (P : Program), 0 < C ∧ Admissible P ∧
      ∀ (nA m s q t : ℕ) (G : RotGraph (Fin nA) (Fin m → ZMod 2)) (u : Fin q → Inner m s) (R : ℕ)
        (Y : Latent (Fin nA) m s q t → ℝ) (ρ : ℝ) {n : ℕ} (ι : Fin n ↪ Fin nA)
        (Cb : BinaryLinearCode n),
        (∀ z, Y z = 1 ∨ Y z = -1) → 0 < ρ → ρ ≤ 1 → (∀ a, (fromW G u t a).card ≤ R) →
        RunsWithin P (structInput G u t [(R : ℤ)] (fun _ => 0) [ρ] (latentBank Y) [])
          (K * ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + nA + q * s * m + 1)
            * Real.logb 2 ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + 2) ^ p
            * (((R : ℝ) + 1) * ((t : ℝ) + 1) / ρ) ^ c)
          (fun out => ∃ x : WIdx G u t → Fin (1 + Mparam (alphaP R t ρ) ρ
              * deltaDim C (alphaP R t ρ) ρ (Fintype.card (Latent (Fin nA) m s q t)) R) → ℝ,
            EncodesVectors out x ∧ GoodVectors G u t ι Cb Y ρ (alphaP R t ρ) x) (1 / 2) := by sorry

end ExpanderWalkDecode.Main
