-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_lemma_6
-- name    : AdWordsMSVV.Tradeoff.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:21.146766+00:00
-- url     : https://prove2.me/theorems/55f81cb8-4fa3-46bd-9760-e47c3a7b59c2
-- title:
--   Lemma 6, p. 11 — OPT(q) ψ(type(q)) ≤ ALG(q) ψ(slab(q)) for every query with 1 ≤ type(q) ≤ k − 1
-- statement:
--   Fix $k\ge1$ slabs, a tradeoff function $\psi$ that is monotonically decreasing on $\{1,\dots,k\}$, an adwords instance with unit budgets and nonnegative bids $c_{b,t}$, and a run $\sigma$ of the discrete algorithm with tradeoff function $\psi$. Let $\tau$ be any allocation (the "OPT" of the paper), and let $q$ be the query at position $t$, which $\tau$ assigns to bidder $b$. If the type of $b$ at the end of the run satisfies $1\le\mathrm{type}(b)\le k-1$, then
--   $$c_{b,t}\,\psi(\mathrm{type}(b))\le\mathrm{ALG}(q)\,\psi(\mathrm{slab}(q)),$$
--   where $\mathrm{ALG}(q)$ is the bid of the bidder to whom the run assigns $q$ and $\mathrm{slab}(q)$ is that bidder's active slab when $q$ arrives.
--
--   The left side is $\mathrm{OPT}(q)\psi(\mathrm{type}(q))$ in the paper's notation. The inequality is the per-query comparison summed in Lemma 7.
--
--   **Formalization Note** The lemma uses no optimality of $\tau$, so it is stated for every allocation. Monotonicity of $\psi$ is assumed on the slab range $\{1,\dots,k\}$ only.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 11, Lemma 6 (with the Definition of ALG(q), OPT(q), type and slab of a query, p. 11)

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting

namespace AdWordsMSVV.Tradeoff
theorem lemma_6 {N M : ℕ} (k : ℕ) (hk : 1 ≤ k) (ψ : ℕ → ℝ)
    (hψ : AntitoneOn ψ (Set.Icc 1 k))
    (bid : Fin N → Fin M → ℝ) (hbid : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (hσ : IsRun ψ k bid σ)
    (τ : Fin M → Option (Fin N)) (t : Fin M) (b : Fin N) (hτ : τ t = some b)
    (htype : 1 ≤ typeOf k bid σ b ∧ typeOf k bid σ b ≤ k - 1) :
    bid b t * ψ (typeOf k bid σ b) ≤ algRev bid σ t * ψ (slabQ k bid σ t) := by sorry
end AdWordsMSVV.Tradeoff
