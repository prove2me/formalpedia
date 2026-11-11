-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_lemma2_operator_recovery
-- name    : ExpanderWalkDecode.Main.lemma2_operator_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:42.979256+00:00
-- url     : https://prove2.me/theorems/5299ef19-b531-424c-9324-5282088406ac
-- title:
--   Lemma 2 (Step 2 Analysis) — the operators of Figure 3 in time $O(N)\,\mathrm{poly}(DR)$, good on good vectors
-- statement:
--   There are constants $K$, $c$ and one deterministic program such that, for every walk structure, $R\ge|\mathrm{WRW}^{\le t}_s(a)|$, $d$, $\rho>0$ and vectors $\{x_{\vec a}\}\subset\mathbb R^d$ (given as records in any order):
--
--   1. the program halts within $K(N+|A|+qsm+1)\,((d+1)(R+1))^c$ steps and outputs exactly the operators $T_a=2\Pi_a-I$ of Figure 3;
--   2. if moreover $A$ is locally invertible, $\rho\le1$, $Y\in\{\pm1\}$, and the vectors are good (Definition 2, with $\alpha=10240R^2(t+1)^3/\rho^8$, for $\mathrm{LIST}(Y,\rho)$ of a base code $C_{\mathrm{base}}$ with embedding $\iota$), then $\{T_a\}$ are good parity operators (Definition 4).
--
--   This is Step 2 of the decoder.
--
--   Differences from the source:
--   - generalization: the paper's walk structure (graphs of Proposition 3, base code of Proposition 1) → any outer graph with ports F_2^m, any inner Cayley graph on (F_2^m)^s, any t, any base code and embedding; reason: the statement uses no expansion property; specializes to the paper's structure
--   - reading: E_{a∼A} E_{⃗a,⃗a′∼WRW^{≤t}_s(a)} in G(P) → ⃗a, ⃗a′ drawn uniformly from the set WRW^{≤t}_s(a); reason: the source gives no other law on walks of mixed lengths; Claim 11's proof bounds sums over WRW^{≤t}_s(a) by R times this average
--   - reading: D_parity.op (the algorithm in Figure 3) runs in time O(N)·poly(DR) and outputs good parity operators → a program outputs exactly the Figure 3 operators within K(N + |A| + qsm + 1)((d+1)(R+1))^c steps, and these are good when the input is good; reason: the input size of a general walk structure; Figure 3 is deterministic
--   - reading: good input vectors (in the construction, whose outer graph is locally invertible) → local invertibility of A among the hypotheses of the goodness clause; reason: standing property of the outer graph (Appendix B.1), used through Claim 11
--   - generalization: a received word on the support set of wide replacement walks → an arbitrary received sign word on the full latent-coordinate space; reason: a source word pulls back along the walk map; all copies of a support coordinate then have the same received sign. The extension keeps the latent sampling law and charges every coordinate
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 14 (PDF p. 17), §4.2, Lemma 2

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Lemma 2 (Step 2 Analysis) (§4.2, p. 14): one deterministic program computes the operators
`T_a = 2Π_a - I` of Figure 3 from the vectors in time `O(N) poly(DR)`; and whenever the input
vectors are good (Definition 2, with `α` of §4.1 and `R ≥ |WRW^{≤t}_s(a)|`), these operators are
good parity operators (Definition 4). -/
theorem lemma2_operator_recovery :
    ∃ (K c : ℝ) (P : Program), Admissible P ∧
      ∀ (nA m s q t : ℕ) (G : RotGraph (Fin nA) (Fin m → ZMod 2)) (u : Fin q → Inner m s) (R d : ℕ) (ρ : ℝ)
        (x : WIdx G u t → Fin d → ℝ) (l : List (WIdx G u t)),
        0 < ρ → (∀ a, (fromW G u t a).card ≤ R) → Enumerates l →
        RunsWithin P (structInput G u t [(R : ℤ), (d : ℤ)] (fun _ => 0) [ρ] (fun _ => 0)
            (vectorRecords l x))
          (K * ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + nA + q * s * m + 1)
            * (((d : ℝ) + 1) * ((R : ℝ) + 1)) ^ c)
          (fun out => out = opsList (figure3T G u x ρ)) 1 ∧
        ∀ (Y : Latent (Fin nA) m s q t → ℝ) {n : ℕ} (ι : Fin n ↪ Fin nA) (Cb : BinaryLinearCode n),
          (∀ z, Y z = 1 ∨ Y z = -1) → ρ ≤ 1 → G.LocallyInvertible →
          GoodVectors G u t ι Cb Y ρ (alphaP R t ρ) x →
          GoodParityOps G u t ι Cb Y ρ R (figure3T G u x ρ) := by sorry

end ExpanderWalkDecode.Main
