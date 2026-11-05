-- Prove2me | Theorems.Thm_BlindNRMLS_lemma_EC_3
-- name    : BlindNRMLS.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:58.810347+00:00
-- url     : https://prove2.me/theorems/54050903-95c0-4165-b3d3-d384e5980453
-- title:
--   Lemma EC.3 (corrected: stated for $I_\mu$; the noise terms carry no $\xi$) — imbalanced use of a family loses revenue
-- statement:
--   Let $b\in(0,1]^d$, $T\ge1$, $d\ge1$, $K\ge d+1$, $n\ge d+1$, $\zeta\in[0,1)$, $\xi\in(0,1]$ and $\eta\in[0,\frac12]$. Take $\mu_{1,k}=\eta/(d+1)$ if $k\%(d+1)=1$, $-\eta/(d+1)$ if $k\%(d+1)=0$, $0$ otherwise, and $\mu_{2,k}=\eta$. Then $J^{\mathrm{DLP}}=T/2$ on $I_\mu$, and every policy $\pi$ that with probability at least $\xi$ uses some family $\mathcal A_l$ for at most $\zeta T/(d+1)$ selling periods satisfies
--   $$
--   \mathrm{Rev}(\pi)\le J^{\mathrm{DLP}}-\xi J^{\mathrm{DLP}}\frac{(1-\zeta)\eta}{d(d+1)^2}+2\sqrt{3KT\log T}+\frac6{T^2}.
--   $$
--   The optimal LP solution must use all families, so any policy that neglects one loses a linear amount. This is what forces $d$ extra switches in the lower bound.
--
--   Differences from the source:
--   - correction: the lemma is stated for an SP instance with Bernoulli costs of mean b_i/2 ± b_iη → it is stated for I_µ, with consumption 2b_i Ber(·); reason: Theorem 4 applies it to I_µ, whose law differs
--   - correction: the noise terms carry the factor ξ and min b_i: −ξJ(…−(1/min b_i)√(3K log T)T^{-1/2}) + ξ√(3KT log T) → noise terms 2√(3KT log T) + 6/T² with no ξ; reason: the clean-event slack is paid on every path: T=K=2, d=1, b₁=0.1, η=½, ζ=0, ξ=0.01, π≡arm 1 has Rev=1.2825 > 1.1718
--   - generalization: b ∈ (0,1)^d → b ∈ (0,1]^d; reason: Theorem 4 allows B_i/T = 1; the page's b ∈ (0,1)^d is a special case
--   - reading: "selects some family … with probability ξ" → at least ξ, with plays counted within the selling horizon; reason: the way Theorem 4 uses it; the proof is per action sequence, and periods after a stop earn nothing
--   - generalization: J^DLP is not evaluated in the statement → the conclusion adds J^DLP = T/2; reason: Step 1 of the proof, p.ec43; the lower bound needs the value
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Lemma EC.3, p.ec42; Step 1 of the proof of Lemma EC.2, p.ec43

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Lemma EC.3 (corrected): on the hard problem with the `µ` of the lemma, a policy that with
probability at least `ξ` uses some family `A_l` for at most `ζT/(d+1)` selling periods earns
`Rev ≤ J - ξ J (1-ζ)η/(d(d+1)²) + 2√(3KT log T) + 6/T²`, and `J = T/2`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Lemma EC.3, p.ec42, with Step 1 of its proof, p.ec43.

**Formalization Note.** The page states the lemma for an SP instance, while Theorem 4 applies it to
`I_µ`, whose consumption is `2 b_i Ber(·)`: it is stated here for `I_µ`. The noise terms carry no `ξ`,
since the clean-event slack is paid on every path. The page's range `T ≥ 1`, `K ≥ d + 1` is kept:
when `T = 1` or `K > T` the right side exceeds `T ≥ Rev`. `b ∈ (0,1]^d`, since Theorem 4 allows
`B_i/T = 1`. The family's uses are counted within the selling horizon. -/
theorem lemma_EC_3 (T d n K : ℕ) (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (ζ ξ η : ℝ)
    (hb_pos : ∀ i, 0 < b i) (hb_le : ∀ i, b i ≤ 1) (hT : 1 ≤ T) (hd : 1 ≤ d) (hdK : d + 1 ≤ K)
    (hdn : d + 1 ≤ n) (hζ₀ : 0 ≤ ζ) (hζ₁ : ζ < 1) (hξ₀ : 0 < ξ) (hξ₁ : ξ ≤ 1)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 2) (π : Policy n K)
    (hπ : ξ ≤ ((historyLaw (hardLaw d (ec3Mu d η) (fun _ => η)) π T)
      {h | ∃ l : Fin (d + 1), ((∑ k ∈ family d l, soldCount (hardProblem T b hb n K) h k : ℕ) : ℝ) ≤
        ζ * (T : ℝ) / ((d : ℝ) + 1)}).toReal) :
    J (hardProblem T b hb n K) (hardLaw d (ec3Mu d η) (fun _ => η)) = (T : ℝ) / 2 ∧
    Rev (hardProblem T b hb n K) (hardLaw d (ec3Mu d η) (fun _ => η)) π ≤
      J (hardProblem T b hb n K) (hardLaw d (ec3Mu d η) (fun _ => η)) -
        ξ * J (hardProblem T b hb n K) (hardLaw d (ec3Mu d η) (fun _ => η)) *
          ((1 - ζ) * η / ((d : ℝ) * ((d : ℝ) + 1) ^ 2)) +
        2 * Real.sqrt (3 * (K : ℝ) * (T : ℝ) * Real.log T) + 6 / (T : ℝ) ^ 2 := by sorry

end BlindNRMLS
