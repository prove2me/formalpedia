-- Prove2me | Theorems.Thm_CoDecompFO_observation_5_79
-- name    : CoDecompFO.observation_5_79
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:28.026206+00:00
-- url     : https://prove2.me/theorems/ba42a224-fa5c-4a70-bdf3-3333122eea51
-- title:
--   Observation 5.79 (corrected: the full strategy's projection, not the table of all supported hypotheticals) — the bottom-up computation
-- statement:
--   The bottom-up computation, for the projections of the **full strategy** $S^{\mathrm{full}}$.
--
--   1. For $\sigma$-structures $\hat A,\hat B$ and maps $a:\hat A\to P$, $b:\hat B\to Q$, $g:P\to K$, $h:Q\to K$, let $\hat X=\hat A\times_K\hat B$ along $g\circ a$ and $h\circ b$, and let $\rho:\hat X\to P\times_K Q$ be $\rho(\hat x_1,\hat x_2)=(a(\hat x_1),b(\hat x_2))$. Then, for every level and every assignment $\beta$ to $\hat X$ with coordinates $\beta_1,\beta_2$,
--   $$
--   \rho_*\big(S^{\mathrm{full}}[\hat X]_\beta\big)=a_*\big(S^{\mathrm{full}}[\hat A]_{\beta_1}\big)\times_K b_*\big(S^{\mathrm{full}}[\hat B]_{\beta_2}\big),
--   $$
--   where $\times_K$ is the reduced pullback of hypotheticals.
--   2. Let $\mathcal T$ be rooted at $r$, let $c$ be a child of $t$ along the edge $e$, and let $U$ be the partial structure on the subtree at $t$ without the subtree at $c$, with projection $\pi'_t:U\to G_t$. Then the table $H_t=(\pi_t)_*(S^{\mathrm{full}}[G[t]])$ is the projection to $G_t$ of the reduced pullback over $G_e$ of $H_c$ and $(\pi'_t)_*(S^{\mathrm{full}}[U])$.
--   3. For the single node $t$, the table is the induced hypothetical of the full strategy on the bag $G_t$.
--
--   Each table has the size bounded by Lemma 5.81, which yields the claimed computation.
--
--   Differences from the source:
--   - correction: the recurrences of Lemmas 4.27 and 4.28 remain valid for the supported hypotheticals at every node → the single table of the full strategy's projection, computed by reduced pullbacks; reason: the printed form rejects a true sentence: with unary R₁, R₂, bags A = {a₀,a₁} (R₁ = {a₁}, R₂ = A), B = {b₀,b₁} (R₁ = B, R₂ = {b₁}) and a one-point adhesion, ∀x∃y (R₂(x) ↔ R₁(y)) holds in A × B, while reduced pullbacks give only product strategies S_A(x₁) × S_B(x₂), and none of them wins
--   - generalization: bags and adhesions with epimorphisms in the recurrences → clause 1 for any structures and plain maps, any level and any assignment; reason: surjectivity is not used, and bags and adhesions with their maps are a special case
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Observation 5.79, ¶5.80, p.41

import Mathlib
import Definitions.Def_CoDecompFO_HTh
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Observation 5.79**, corrected to the full strategy's projection (Bumpus et al., arXiv:2611.04658,
held file sha256 d550d7af…, p.41): "The dynamic programming recurrences of Lemmas 4.27 and 4.28 remain
valid for supported hypotheticals under the dictionary of Table 1. In particular, the supported
hypotheticals at every node can be computed bottom-up using only projections, the canonical comparison
maps S[f]: f_*(S[G]) → f_*(S)[H], and pullbacks in the total category of hypotheticals."

Three clauses. (1) The reduced pullback of the full strategy's projections from `Â` and `B̂` is the
projection of the full strategy on their pullback `X̂ = Â ×_K B̂`, for all `a`, `b`, `g`, `h`, `m` and
every assignment `l`. (2) In a tree rooted at `r`, the table `H_t := (π_t)_*(S^full[G[t]])` is obtained
from the table at a child `c` and the table of the rest `S = subtree(t) ∖ subtree(c)` of the subtree at
`t`, by a pullback over the adhesion and a projection. (3) At a single node, the table is the induced
hypothetical of the full strategy on the bag (¶5.80: "at a leaf, supported hypotheticals are simply
induced hypotheticals on the bag").

**Formalization Note** The printed form, for the table of all supported hypotheticals, is false. Take `σ =
{R₁,R₂}` unary, `A = {a₀,a₁}` with `R₁ = {a₁}`, `R₂ = A`, `B = {b₀,b₁}` with `R₁ = B`, `R₂ = {b₁}`, and a
one-point adhesion with both relations full. Then `∀x∃y (R₂(x) ↔ R₁(y))` holds in `A × B`. The reduced
local strategies have one personality at each point, so the pullback's responses are exactly the
products `S_A(x₁) × S_B(x₂)`, and no such product wins. Over the full strategy, every compatible pair of
responses is a real point of the pullback, so the pullback is exact. Surjectivity is not used in
clause (1). -/
theorem observation_5_79 {σ : Sig} :
    (∀ (Ah Bh P Q K : Type) [σ.lang.Structure Ah] [σ.lang.Structure Bh]
      (a : Ah → P) (b : Bh → Q) (g : P → K) (h : Q → K) (k m : ℕ)
      (l : List (Fib (g ∘ a) (h ∘ b))),
      push (σ := σ) (k := k)
          (fun z : Fib (g ∘ a) (h ∘ b) => (⟨a z.fst, b z.snd, z.eq⟩ : Fib g h)) m
          (ind σ k m (Strat.full _ m) l) =
        pb g h m
          (push a m (ind σ k m (Strat.full _ m) (l.map Fib.fst)))
          (push b m (ind σ k m (Strat.full _ m) (l.map Fib.snd)))) ∧
    (∀ (T : CoDecomp σ) (r t : Fin T.b) (e : Fin T.m) (he : T.IsChildEdge r t e)
      (hS : t ∈ T.subtree r t \ T.subtree r (T.child e t)) (k m : ℕ),
      push (T.partialProj r t) m (ind σ k m (Strat.full _ m) []) =
        push (Fib.snd :
            Fib (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) →
              Fin (T.bag t).n) m
          (pb (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) m
            (push (T.partialProj r (T.child e t)) m (ind σ k m (Strat.full _ m) []))
            (push (CoDecomp.LimOn.proj t hS) m (ind σ k m (Strat.full _ m) [])))) ∧
    (∀ (T : CoDecomp σ) (t : Fin T.b) (k m : ℕ),
      push (CoDecomp.LimOn.proj (S := {t}) t rfl) m (ind σ k m (Strat.full _ m) []) =
        ind σ k m (Strat.full _ m) []) := by sorry

end CoDecompFO
