-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_lemma_4_2
-- name    : DirKKTBilevel.VP.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:22:49.786234+00:00
-- url     : https://prove2.me/theorems/ba0696bd-9a89-4f17-a742-594397da206c
-- title:
--   Lemma 4.2 (used in the proof of Theorem 4.1; corrected: Ω_u ⊆ ℝᵐ) — consequences of restricted inf-compactness and directional RS
-- statement:
--   Let $f,g$ be continuously differentiable. Suppose the restricted inf-compactness holds at $\bar x$ in direction $u$ with compact set $\Omega_u\subseteq\mathbb R^m$, and $\bar y\in S(\bar x)$ is such that $\mathcal F$ satisfies RS at $(\bar x,\bar y)$ in direction $u$. Then
--   1. $D_+\mathcal F(\bar x,\bar y;u)=L(\bar x,\bar y;u)\neq\emptyset$;
--   2. $\bar y\in\liminf_{x\xrightarrow{u}\bar x}\mathcal F(x)$;
--   3. $S(\bar x;u)\neq\emptyset$;
--   4. for every $l>0$ there are $\varepsilon,\delta>0$ such that every $x\in\bar x+V_{\varepsilon,\delta}(u)$ admits $y\in S(x)\cap\Omega_u$ with
--   $$\operatorname{dist}\big(y,\,S(\bar x;u)\cap\Omega_u\big)<l.$$
--   This lemma localizes lower-level optimizers near the directional solution set; it supports Theorem 4.1 and Proposition 4.3.
--
--   Differences from the source:
--   - correction: Definition 4.1 (p. 13) places the compact set Ω_u in ℝⁿ → Ω : Set (E m), a set of lower-level variables in ℝᵐ; reason: Ω_u must meet S(x) ⊆ ℝᵐ, and the proofs of Lemma 4.2 (p. 16) and Proposition 4.3 (p. 17) take limits ỹ ∈ Ω_u of lower-level solutions; ℝⁿ is a dimension slip. No case is excluded.
--   - reading: Definitions 2.3 and 4.4 (pp. 6, 13) ask for y_k ∈ Φ(x̄ + t_k u_k) without saying for which k → dirLiminf and IsDirInnerSemicont require y_k ∈ Φ(x̄ + t_k u_k) for all sufficiently large k; reason: this is the Painlevé–Kuratowski convention the paper says it recovers at u = 0 (p. 6); requiring every k would force Φ(x) ≠ ∅ at every point x ≠ x̄, since any point is the first term of some admissible sequence, and the proofs (pp. 16, 18) only use large k.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 15, Lemma 4.2

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Lemma 4.2, p. 15: suppose the restricted inf-compactness holds at `x̄` in direction `u` with the
compact set `Ω`, and `ȳ ∈ S(x̄)` is such that `𝓕` satisfies RS at `(x̄, ȳ)` in direction `u`. Then
`D₊𝓕(x̄, ȳ; u) = L(x̄, ȳ; u) ≠ ∅`, `ȳ ∈ liminf_{x →ᵤ x̄} 𝓕(x)` and `S(x̄; u) ≠ ∅`; and for every
`l > 0` there are `ε, δ > 0` such that every `x ∈ x̄ + V_{ε,δ}(u)` admits `y ∈ S(x) ∩ Ω` with
`dist(y, S(x̄; u) ∩ Ω) < l`. -/
theorem lemma_4_2 {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x u : E n) (Ω : Set (E m)) (y : E m)
    (hRIC : IsRestrInfCompactDir f g x u Ω) (hy : y ∈ solMap f g x) (hRS : IsRSDir g x y u) :
    diniFeas g x y u = linLL g x y u ∧ (linLL g x y u).Nonempty ∧
      y ∈ dirLiminf (feasLL g) x u ∧ (dirSol f g x u).Nonempty ∧
      ∀ l : ℝ, 0 < l → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ x', x' - x ∈ dirNbhd ε δ u →
        ∃ y' ∈ solMap f g x' ∩ Ω,
          Metric.infEDist y' (dirSol f g x u ∩ Ω) < ENNReal.ofReal l := by sorry

end DirKKTBilevel.VP.Supplement
