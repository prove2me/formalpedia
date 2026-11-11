-- Prove2me | Theorems.Thm_ContinualHardness_Linear_theorem_A_8
-- name    : ContinualHardness.Linear.theorem_A_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:13:04.15791+00:00
-- url     : https://prove2.me/theorems/c20582d7-1897-4a80-aa04-48e3985f7bc0
-- title:
--   Theorem A.8 — polynomial-time reduction from Smooth-Label-Cover (Q, R of (15)) to T separable symmetric datasets: YES gives a common (1 − ε)-accurate classifier, NO at most one task above 1/2 + δ
-- statement:
--   Let $\varepsilon,\delta>0$ and an integer $T>1$; let $c_0>0$ (the constant of Theorem A.3) and let $c_1$ be a Berry–Esseen constant (Theorem A.1). Let $\tau=\frac{\delta}{4c_1}\sqrt{\varepsilon/T}$ as in (7), and $R$, $q=4^R$, $Q$ as in (15):
--   $$R=\max\Big(1,\Big\lceil\tfrac1{c_0}\log_2\tfrac{2^{12}}{\delta^2\tau^4}\Big\rceil\Big),\qquad Q=\max\Big(1,\Big\lceil\tfrac{2^{12}q^2}{\tau^4\delta^2}\Big\rceil\Big).$$
--   Then there is a polynomial-time computable map $g$ on bit strings (Cook's Turing machines, `CookPvsNP.PolyTimeComputable`) such that for every Smooth-Label-Cover instance $L$ with the properties of Theorem A.3 for $Q,R$ (`Props Q R`), $g(\mathrm{enc}(L))$ is the code of an instance with $T$ datasets $D_1,\dots,D_T$ in $\mathbb R^d\times\{-1,1\}$ (rational data) such that:
--   * (**Tractability of individual tasks**) every $D_t$ is a finite symmetric dataset separable by a homogeneous linear classifier $\operatorname{sign}((r^{(t)})^{\mathsf T}x)$;
--   * (**YES Case**) if some labeling satisfies every edge of $L$, there is $r^*\in\mathbb R^d$ with $\mathrm{Acc}(D_t,\operatorname{sign}((r^*)^{\mathsf T}x))\ge1-\varepsilon$ for every $t$;
--   * (**NO Case**) if every labeling satisfies less than a fraction $2^{-c_0R}$ of the edges, then for every linear classifier $h=\operatorname{sign}(r^{\mathsf T}x+c)$, $r\in\mathbb R^d$, $c\in\mathbb R$,
--   $$\big|\{t:\mathrm{Acc}(D_t,h)>\tfrac12+\delta\}\big|\le1 .$$
--   Composed with Theorem A.3 (applied with $\delta/2$), this gives Theorem 3.1.
--
--   Differences from the source:
--   - reading: R := (1/c0) log(2^12/(δ²τ⁴)) and Q := 2^12 q²/(τ⁴δ²), real numbers → R = max(1, ⌈(1/c0) log₂(2^12/(δ²τ⁴))⌉), Q = max(1, ⌈2^12 q²/(τ⁴δ²)⌉); reason: Theorem A.3 needs integers Q, R ≥ 1; log is read in base 2, the only base for which the comparison at the end of §A.5 yields a contradiction (INSIGHTS I3); Q is stated as printed although the proof's (30) needs q⁴ (INSIGHTS I1)
--   - reading: c0 and c1 are the absolute constants of Theorems A.3 and A.1 → for every c0 > 0 and every c1 with IsBerryEsseenConstant c1; reason: the stronger reading: the reduction is claimed for every such constant, and the proof only uses c0 in R and inequality (5) for c1
--   - encoding: a polynomial time reduction from an SLC instance L to T finite symmetric datasets with data-points from ℝ^d × {−1, 1} → ∃ g : List Bool → List Bool, PolyTimeComputable g, with g(encodeSLC L) = encodeCL I for an instance I with rational coordinates and weights; reason: a polynomial-time output is a finite string; rational data are the standard representation (the reduction may choose a rational basis of F), and classifiers stay real
--   - encoding: L given by Theorem A.3 (a regular connected graph with the listed properties); YES / NO instance → hypothesis L.Props Q R (indexed multigraph, loops and parallel edges allowed, ≥ 1 edge, regular, connected, M, N, smoothness, preimages ≤ 4^R, label weighting, weak expansion); L.Satisfiable; L.ValueBelow (2^(−c0 R)); reason: Lean representation of Definition A.2 and Theorem A.3; fractions of edges presuppose E ≥ 1
--   - encoding: datasets are 'finite symmetric', 'Dt is linearly separable' → CLInstance.Valid: each D_t has non-negative weights summing to 1 on labels ±1, D_t(x, y) = D_t(−x, −y), and some homogeneous linear classifier has accuracy 1; reason: the definitions of §2.1 and Theorem 3.1, condition 1
--   - reading: a regular connected (undirected) graph G(V, E) in Definition A.2 → an edge may be a loop (ends e = (v, v)); a loop lies inside every V′ containing v and counts at both of its ends in the degree; reason: weak expansion as printed needs |E|/|V|² > 0 edges inside a single vertex, so it is unsatisfiable on a loopless graph; the construction of [15] (Appendix B) produces loops (u = v is allowed); INSIGHTS I5
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 19, Theorem A.8 with Eq. (15) (PDF p. 20); pp. 20-24, §A.3-A.5 (PDF pp. 21-25)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Instance
import Definitions.Def_ContinualHardness_Linear_SmoothLabelCover
import Definitions.Def_ContinualHardness_Linear_BerryEsseen
import Definitions.Def_ContinualHardness_Linear_Dict

namespace ContinualHardness.Linear

/-- Theorem A.8, p. 19. Fix `ε, δ > 0`, an integer `T > 1`, a constant `c₀ > 0` (the constant of
Theorem A.3) and a Berry–Esseen constant `c₁`; let `τ = (δ/(4c₁))√(ε/T)` as in (7) and `R`, `Q` as
in (15) (`R = ⌈(1/c₀) log₂(2¹²/(δ²τ⁴))⌉`, `q = 4^R`, `Q = ⌈2¹² q²/(τ⁴δ²)⌉`, both at least `1`).
There is a polynomial-time computable map on binary strings which sends the code of every
Smooth-Label-Cover instance `L` having the properties of Theorem A.3 for `Q, R` to the code of `T`
finite symmetric rational datasets `D₁, …, D_T` in `ℝ^d × {−1, 1}` such that
* (Tractability) each `D_t` is separable by a homogeneous linear classifier;
* (YES Case) if some labeling satisfies every edge of `L`, one homogeneous linear classifier
  `sign((r*)ᵀx)` has `Acc(D_t, ·) ≥ 1 − ε` for every `t`;
* (NO Case) if every labeling satisfies less than a fraction `2^{−c₀R}` of the edges, every linear
  classifier `h = sign(rᵀx + c)` has `Acc(D_t, h) > 1/2 + δ` for at most one `t`. -/
theorem theorem_A_8 (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (T : ℕ) (hT : 1 < T)
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : IsBerryEsseenConstant c₁) :
    ∃ g : List Bool → List Bool, CookPvsNP.PolyTimeComputable g ∧
      ∀ L : SLCInstance,
        L.Props (paramQ δ (dictTau c₁ ε δ T) (paramR c₀ δ (dictTau c₁ ε δ T)))
          (paramR c₀ δ (dictTau c₁ ε δ T)) →
        ∃ I : CLInstance T, g (encodeSLC L) = encodeCL I ∧
          I.Valid ∧
          (L.Satisfiable →
            ∃ r : Fin I.d → ℝ, ∀ t : Fin T, 1 - ε ≤ acc (I.data t) (linClf r 0)) ∧
          (L.ValueBelow ((2 : ℝ) ^ (-(c₀ * (paramR c₀ δ (dictTau c₁ ε δ T) : ℝ)))) →
            ∀ (r : Fin I.d → ℝ) (c : ℝ),
              (Finset.univ.filter fun t : Fin T =>
                1 / 2 + δ < acc (I.data t) (linClf r c)).card ≤ 1) := by sorry

end ContinualHardness.Linear
