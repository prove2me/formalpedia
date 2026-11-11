-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_7
-- name    : ApproxSyzygies.Smoothed.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:48.063405+00:00
-- url     : https://prove2.me/theorems/ef2959f5-be6b-4869-adb0-1eebb82929fc
-- title:
--   Lemma 4.7 — one-step shrinking: with probability $\ge1-me^{-\gamma}$ approximate solutions lie near $G'$ with $\dim G'\le2\sum_iN_G/\dim U_i$
-- statement:
--   Let $W=\bigoplus_{i=1}^mW_i$ and fix a candidate space $G\subseteq W$ with $\dim G\le N_G$. Let $\zeta=(\zeta_1,\dots,\zeta_m)$, $\zeta_i\in U_i$, be independent, each with a $(1/4,\eta_0,\gamma)$-subspace anticoncentrated law, and $\dim U_i\ge4$. Let $C_i:G\to U_i\otimes W_i$ be random linear maps such that $\zeta_i$ is independent of $C_i$ ($C_i$ may depend on the $\zeta_j$, $j\ne i$). Then with probability at least $1-m\,e^{-\gamma}$ there is a subspace $G'\subseteq G$ with
--   $$\dim G'\le2\sum_{i=1}^m\frac{N_G}{\dim U_i}$$
--   such that every $g\in G$ and every $\eta$ satisfy
--   $$\forall i\in[m]:\ \|\zeta_i\otimes g_i+C_i(g)\|\le\eta\ \Longrightarrow\ \mathrm{dist}(g,G')\le\frac{\eta\sqrt{\sum_i\dim(U_i)^2}}{\eta_0}.$$
--   Iterated in Proposition 4.8, it shrinks the space of candidate approximate syzygies to $\{0\}$.
--
--   Differences from the source:
--   - encoding: Euclidean spaces $U$, $W$ and the tensor product $U\otimes W$ → $\mathbb R^{\iota}$, $\mathbb R^{\kappa}$ for finite index types and $\mathbb R^{\iota\times\kappa}$ with $(u\otimes w)_{(a,b)}=u_aw_b$ (`tens`); reason: every finite-dimensional real inner product space is isometric to some $\mathbb R^{\iota}$, and $\mathbb R^{\iota\times\kappa}$ with the Frobenius norm is the Hilbert tensor product
--   - encoding: "$C_i$ can depend on $\zeta_j$ for $j\ne i$, but $\zeta_i$ is independent of $C_i$" → every evaluation $\omega\mapsto C_i(\omega)g$ is measurable for a σ-algebra $\mathcal F_i$ independent of $\sigma(\zeta_i)$; reason: this is independence of $\zeta_i$ and $C_i$ (take $\mathcal F_i=\sigma(C_i)$); dependence on the other $\zeta_j$ is permitted, not required
--   - encoding: independent random vectors drawn from subspace anticoncentrated distributions → measurable $\zeta_i$ on a probability space, `iIndepFun ζ P`, and `SubspaceAnticonc (1/4) η₀ γ (P.map (ζ i))`; reason: random variables are measurable maps; the law of $\zeta_i$ is its push-forward
--   - reading: $\eta$ (free in (19)) → one $G'$ for every $\eta\in\mathbb R$ and every $g\in G$ inside the event; reason: the proof (p. 36) says the same event works simultaneously for every $g$ and every $\eta\ge0$, and Proposition 4.8 uses it so; for $\eta<0$ the premise fails
--   - encoding: "with probability at least $1-m\exp(-\gamma)$" → the (outer) measure of the failure event is at most $m e^{-\gamma}$; reason: the event need not be measurable; the bound on its complement is the same statement
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 33, Lemma 4.7

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

/-- Lemma 4.7 (p. 33): one-step shrinking. `W = ⨁_i W_i` with `W_i = ℝ^{κ_i}`, `U_i = ℝ^{ι_i}`
of dimension at least `4`, a candidate space `G ⊆ W` of dimension at most `N_G`; independent
random `ζ_i ∈ U_i`, each `(1/4, η₀, γ)`-subspace anticoncentrated; random linear maps
`C_i : G → U_i ⊗ W_i` with `ζ_i` independent of `C_i` (`C_i` is measurable for a σ-algebra
`𝓕_i` independent of `ζ_i`). Then, outside an event of probability at most `m e^{−γ}`, there is a
subspace `G' ⊆ G` with `dim G' ≤ 2 ∑_i N_G / dim U_i` such that for every `η` and every
`g ∈ G`, `‖ζ_i ⊗ g_i + C_i(g)‖ ≤ η` for all `i` implies
`dist(g, G') ≤ η √(∑_i (dim U_i)²) / η₀`. -/
theorem lemma_4_7 {m : ℕ} {ι κ : Fin m → Type} [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (G : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i))) (NG : ℕ)
    (hG : Module.finrank ℝ G ≤ NG) (η₀ γ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ζ : ∀ i, Ω → EuclideanSpace ℝ (ι i)) (hζ : ∀ i, Measurable (ζ i))
    (hind : iIndepFun ζ P)
    (hsa : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ (P.map (ζ i)))
    (hdim : ∀ i, 4 ≤ Fintype.card (ι i))
    (C : ∀ i, Ω → (G →L[ℝ] EuclideanSpace ℝ (ι i × κ i)))
    (𝓕 : Fin m → MeasurableSpace Ω) (h𝓕 : ∀ i, 𝓕 i ≤ ‹MeasurableSpace Ω›)
    (hCmeas : ∀ i (g : G), Measurable[𝓕 i] fun ω => C i ω g)
    (hCind : ∀ i, Indep (MeasurableSpace.comap (ζ i) inferInstance) (𝓕 i) P) :
    P {ω | ¬ ∃ G' : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i)), G' ≤ G ∧
          (Module.finrank ℝ G' : ℝ) ≤ 2 * ∑ i, (NG : ℝ) / (Fintype.card (ι i) : ℝ) ∧
          ∀ (η : ℝ) (g : G),
            (∀ i, ‖tens (ζ i ω) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i) + C i ω g‖ ≤ η) →
            Metric.infDist (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) G' ≤
              η * Real.sqrt (∑ i, ((Fintype.card (ι i) : ℝ)) ^ 2) / η₀}
      ≤ ENNReal.ofReal (m * Real.exp (-γ)) := by sorry

end ApproxSyzygies.Smoothed
