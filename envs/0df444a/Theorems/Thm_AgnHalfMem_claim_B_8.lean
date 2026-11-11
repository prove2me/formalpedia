-- Prove2me | Theorems.Thm_AgnHalfMem_claim_B_8
-- name    : AgnHalfMem.claim_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:53.237807+00:00
-- url     : https://prove2.me/theorems/4b8103fa-e804-4b6a-a1f8-3f469e146ee3
-- title:
--   Claim B.8 — Bayes' rule on an edge of the truncated path
-- statement:
--   In the setting of Appendix B (see Lemma B.4), let $e=(v,u)$ be an edge of $B$ from layer $i$, labelled $A_e\subseteq X\times\{-1,1\}$, with $\Pr(e)>0$. For every $h'\in H$,
--   $$
--   P_{h|e}(h')=\begin{cases}0,& h'\in\mathrm{Sig}(v),\\[2pt] \dfrac{P_{h|v}(h')\,q_e(h')}{c_e},& h'\notin\mathrm{Sig}(v),\end{cases}\qquad
--   q_e(h')=\sum_{y\in\{-1,1\}}\int_{\substack{x:(x,y)\in A_e\\ x\notin\mathrm{Bad}(v)}}\frac{1+yM(x,h')}{2}\,d\mu(x),
--   $$
--   where $c_e=\Pr[e\mid E_v]=\Pr(e)/\Pr(v)$ satisfies
--   $$
--   \frac{c_e}{\mu_e}\ \ge\ \frac12-2\cdot2^{-2r},\qquad \mu_e=\sum_{y\in\{-1,1\}}\mu\big(\{x:(x,y)\in A_e,\ x\notin\mathrm{Bad}(v)\}\big).
--   $$
--   It describes how one step of the truncated path updates the posterior on $h$.
--
--   Differences from the source:
--   - encoding: standing assumptions of App. B stated once (p.29: 1/100 < c < 2/3, 3c/2 < γ² < 1, M a (k′,ℓ′)-extractor with error 2^{−r′} "for sufficiently large k′, ℓ′ and r′", B a branching program) → hypotheses AppBConstants c γ; ∃ K₀ (after c, γ) with K₀ ≤ k′, ℓ′, r′; M measurable in x with values in [−1,1] and IsL2Extractor μ M k′ ℓ′ r′; B a measurable deterministic BP on a finite state type S; reason: the section's standing assumptions are hypotheses of every claim; measurability is what makes the probabilities defined
--   - reading: γ with 3c/2 < γ² < 1; "k := γk" → 0 < γ; k = γk′ (appBk); reason: γ scales the exponents k, ℓ; the typo is corrected by p.37 "Recall that k = γk′"
--   - encoding: vertices of layers with at most 2^{ck′ℓ′} vertices, edges with labels A_e, P_{h|v} for Pr(v) > 0 → vertices (i, v) with v in one finite type S; edges (v, u) with A_e = {z | step i v z = u}; P_{h|v} := 0 when Pr(v) = 0; reason: Lean conventions for the layered graph; the zero posterior only arises on null vertices
--   - encoding: c_e = Pr[e | E_v] → edgeProb / vertexProb; reason: E_e ⊆ E_v, so the conditional probability is the ratio
--   - generalization: B of length m = 2^r and width at most 2^{ck′ℓ′} (p.30, “We assume B is a branching program with length m = 2^r and width at most 2^{ck′ℓ′}”) → any length T and any finite state type S, with no length or width bound; reason: the proof works at one vertex or edge and uses neither bound; programs of length 2^r and width at most 2^{ck′ℓ′} are instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.8, p.33 (proof pp.33–35)

import Mathlib
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AppBConstants
import Definitions.Def_AgnHalfMem_truncAlive

open MeasureTheory

universe u v w

namespace AgnHalfMem

/-- **Claim B.8 (Bayes' rule on an edge).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim B.8, p.33: "For any edge e = (v, u)
of B labeled by set A_e ∈ X × {−1, 1} such that Pr(e) > 0, for any h′ ∈ H,
P_{h|e}(h′) = 0 if h′ ∈ Sig(v), P_{h|v}(h′) · q_e(h′)/c_e if h′ ∉ Sig(v), where
q_e(h′) = Σ_{y∈{−1,1}} ∫_{x:(x,y)∈A_e, x∉Bad(v)} (1 + yM(x, h′))/2 dµ(x), and c_e = Pr[e | E_v] is
the normalization constant satisfying c_e/µ_e ≥ 1/2 − 2 · 2^{−2r}, with
µ_e = Σ_{y∈{−1,1}} ∫_{x:(x,y)∈A_e, x∉Bad(v)} dµ(x)."

**Formalization Note.** The standing assumptions of App. B (p.29) are hypotheses: `c, γ` with
`AppBConstants c γ`; `M : X × H → [−1, 1]` measurable in `x`, a `(k′, ℓ′)`-L2-extractor with error
`2^{−r′}` for `k′, ℓ′, r′ ≥ K₀` ("sufficiently large", `K₀` chosen after `c, γ`); `ℓ = γℓ′/3`
(`appBl`), `r` as on p.29 (`appBr`), `k = γk′` (`appBk`); `B` a deterministic, measurable
program of length `T` on the states `S`. Vertices are pairs (layer `i`, state `v`); all
probabilities are under the joint law (`h` uniform, samples i.i.d. from `D_h`); `P_{h|v} = 0` when
`Pr(v) = 0`. The edge `e = (v, u)` from layer `i` carries `A_e = {z | step i v z = u}`;
`c_e = Pr(e)/Pr(v)` (`E_e ⊆ E_v`); labels `y` are `Bool` with value `sgn y`. -/
theorem claim_B_8 :
    ∀ c γ : ℝ, AppBConstants c γ →
    ∃ K₀ : ℝ,
    ∀ (H : Type u) [Fintype H] [Nonempty H] [MeasurableSpace H] [DiscreteMeasurableSpace H]
        (X : Type v) [MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (M : X → H → ℝ), (∀ h, Measurable fun x => M x h) →
        (∀ x h, M x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ k' l' r' : ℝ, IsL2Extractor μ M k' l' r' → K₀ ≤ k' → K₀ ≤ l' → K₀ ≤ r' →
      ∀ (S : Type w) [Fintype S] (T : ℕ) (B : BP S X T), B.IsMeasurableBP →
      ∀ (i : ℕ) (v u : S), 0 < edgeProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v u →
        (∀ h', h' ∈ Sig (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (appBl γ l') (appBr γ k' l' r') →
          edgePost μ M B (appBl γ l') (appBr γ k' l' r') r' i v u h' = 0) ∧
        (∀ h', h' ∉ Sig (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) (appBl γ l') (appBr γ k' l' r') →
          edgePost μ M B (appBl γ l') (appBr γ k' l' r') r' i v u h' =
            vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v h' *
              (∑ y : Bool, ∫ x in {x | B.step i v (x, y) = u ∧
                  x ∉ Bad M (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) r'}, (1 + sgn y * M x h') / 2 ∂μ) /
              (edgeProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v u / vertexProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v)) ∧
        1 / 2 - 2 * (2 : ℝ) ^ (-(2 * appBr γ k' l' r')) ≤
          (edgeProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v u / vertexProb μ M B (appBl γ l') (appBr γ k' l' r') r' i v) /
            (∑ y : Bool, (μ {x | B.step i v (x, y) = u ∧
                x ∉ Bad M (vertexPost μ M B (appBl γ l') (appBr γ k' l' r') r' i v) r'}).toReal) := by sorry

end AgnHalfMem
