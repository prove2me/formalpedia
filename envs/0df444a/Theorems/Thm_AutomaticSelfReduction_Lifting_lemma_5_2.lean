-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_lemma_5_2
-- name    : AutomaticSelfReduction.Lifting.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:58.906687+00:00
-- url     : https://prove2.me/theorems/8d2cca27-f486-4fb2-a2e9-65c70504a6d0
-- title:
--   Lemma 5.2 — one-round speedup with error factor 16(1+b) and zero error on the new active side
-- statement:
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized 2-separated $b$-dominant problem, let $(S,\mu)$ be a shared-randomness probability space, let $T\ge1$, and let $\mathcal G$ be a class of $(\Delta,\delta)$-biregular 2-coloured graphs on $n$ vertices, each of girth at least $2T+3$. Suppose $A$ is a $T$-round algorithm for $\Pi$ which, on every graph of $\mathcal G$, has expected white error $0$ and expected error at most $\varepsilon$.
--
--   Then there is a $(T-1)$-round algorithm $A'$ for $\Pi'=R(\Pi)$, run by the nodes that are black in $\Pi$, such that
--
--   1. $A'$ outputs a configuration of the active constraint $C'_B$ of $R(\Pi)$ on every execution (black error $0$ in the colours of $\Pi$), and
--   2. on every graph $G\in\mathcal G$,
--   $$
--   \mathbb E\bigl[\operatorname{err}_{R(\Pi)}(A',G)\bigr]\le 16(1+b)\,\varepsilon .
--   $$
--
--   Because the conclusion has the same form as the hypothesis with the active side exchanged, the lemma can be applied repeatedly; this iteration yields the lower bound of Theorem 5.1.
--
--   **Formalization Note** $R(\Pi)$ has active degree $\delta$, so $A'$ runs on `G.swap`, the same graph with colours exchanged. The hypothesis "white error 0" is read as expected white error $0$ on each graph (equivalently almost surely); the conclusion "black error 0" holds on every execution. The model is the randomized LOCAL model of the definition file: full-information states, uniformly random port orders, infinite fair private bit strings, arbitrary shared randomness, measurable rules.
--
--   Differences from the source:
--   - generalization: in graphs with girth at least 2T + 3 → for every class 𝒢 of n-vertex (Δ,δ)-biregular graphs all of girth ≥ 2T+3, A' achieves the bound on the same class 𝒢; reason: the class of all such graphs is one instance, and the iteration in Theorem 5.1 needs the guarantee on the same family
--   - reading: white error 0 (hypothesis) and black error 0 (conclusion) → expected white error 0 on each graph of 𝒢, and validity of A' on every execution; reason: the paper does not say whether almost surely or always; this is the weaker hypothesis and the stronger conclusion
--   - encoding: R(Π) solved on the same graph by the former black nodes → A' is an algorithm for R P on G.swap; reason: in R(Π) = (Σ', δ, Δ, C'_B, C'_W) the active side has degree δ; the colour swap only renames the sides
--   - reading: ports "assigned by the nodes using their own random bits", replacing w.l.o.g. an adversarial assignment (§4) → each node's port order is uniformly random, independent of its random bits and of all other nodes' randomness; reason: the source does not fix the law of the assignment; a uniform independent order is the reading under which the w.l.o.g. remark holds and the conditional law of a neighbour's output in §5.1 does not depend on port numbers the black node cannot see
--   - encoding: randomized LOCAL model with unbounded messages, private random bit strings and shared randomness → full-information states, infinite product of fair coins per node, arbitrary probability space (S, μ), measurable rules; reason: messages are unbounded, so every protocol's output is a function of the full-information state; a one-point S is private randomness only
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Lemma 5.2, printed pp. 12–13 (PDF pp. 13–14); remarks on zero white error and the symmetric form, printed p. 13 (PDF p. 14); proof in §5.1–§5.4, printed pp. 13–21

import Definitions.Def_AutomaticSelfReduction_Lifting_Local

open MeasureTheory

namespace AutomaticSelfReduction.Lifting

/-- Lemma 5.2 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF pp. 13–14, printed
pp. 12–13). Let `Π` be a normalized 2-separated `b`-dominant problem and `𝒢` a class of
`(Δ, δ)`-biregular 2-coloured graphs on `n` vertices, all of girth at least `2T + 3`, `T ≥ 1`.
If a `T`-round algorithm `A` for `Π` (with shared randomness `μ`) has white error `0` and
expected error at most `ε` on every graph of `𝒢`, then there is a `(T − 1)`-round algorithm `A'`
for `R(Π)`, run by the former black nodes (the colours are exchanged: `G.swap`), which outputs a
configuration of the active constraint `C'_B` of `R(Π)` on every execution (black error `0` in the
paper's colours) and has expected error at most `16(1 + b) ε` on every graph of `𝒢`. -/
theorem lemma_5_2 {L : Type} [Fintype L] [DecidableEq L] {Δ δ : ℕ} (P : Problem L Δ δ)
    (hN : P.IsNormalized) (h2 : P.TwoSeparated) (b : ℕ) (hb : P.Dominant b)
    {S : Type} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (n T : ℕ) (hT : 1 ≤ T) (𝒢 : Set (Instance n Δ δ))
    (hgirth : ∀ G ∈ 𝒢, G.GirthAtLeast (2 * T + 3))
    (ε : ℝ) (A : Algorithm S L Δ δ T)
    (hA : ∀ G ∈ 𝒢, expWhiteError P μ A G = 0 ∧ expError P μ A G ≤ ENNReal.ofReal ε) :
    ∃ A' : Algorithm S (RLabel P) δ Δ (T - 1),
      A'.WhiteValid (R P) ∧
        ∀ G ∈ 𝒢, expError (R P) μ A' G.swap ≤ ENNReal.ofReal (16 * (1 + b) * ε) := by sorry

end AutomaticSelfReduction.Lifting
