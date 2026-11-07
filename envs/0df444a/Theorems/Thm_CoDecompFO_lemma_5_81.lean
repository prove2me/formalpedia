-- Prove2me | Theorems.Thm_CoDecompFO_lemma_5_81
-- name    : CoDecompFO.lemma_5_81
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:12.136042+00:00
-- url     : https://prove2.me/theorems/c4dd96a1-14c1-43ca-9ff5-c3e5486636fc
-- title:
--   Lemma 5.81 with ¶5.82 — at most a tower of reduced hypotheticals over a bag
-- statement:
--   Fix a signature $\sigma$, a formula with $\ell$ alternations, and a width $w$. Over a bag of size $n\le w$, the set of $m$-hypotheticals on $[2\ell]$ is finite and has at most $h_m$ elements, where $q=\sum_{R\in\sigma}(2\ell)^{\mathrm{ar}(R)}$, and
--   $$
--   h_0=2^{2^q},\qquad h_{m+1}=2^{w\,2^{w\,h_m}} .
--   $$
--   At $m=\ell$ this is the printed tower with $2\ell+2$ exponential layers, a function of $w$ and $|\varphi|$.
--
--   It bounds the work per node by a function of the parameters alone, which is the source of the running time.
--
--   Differences from the source:
--   - generalization: the bound h_ℓ at the top level ℓ → the bound at every level m, for any ℓ, with finiteness stated; reason: the printed bound is the case m = ℓ
--   - encoding: reduced hypotheticals (¶5.37), counted through "reduced families" → the set-level recursive type; reason: Prop. 5.38 identifies the two, and sets carry one entry per subset
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.81, ¶5.82, p.41

import Mathlib
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Lemma 5.81 with ¶5.82** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, p.41): "For
fixed signature σ, formula φ, and width w, the number of reduced hypotheticals that can occur over a bag
of size at most w is bounded by a function of w and |φ|", explicitly `h_ℓ ≤ 2^{w 2^{w 2^{⋯ w 2^{w 2^{2^q}}}}}`
(`2ℓ+2` exponential layers), where `q := ∑_{R∈σ} (2ℓ)^{ar(R)}`.

**Formalization Note** The type of `m`-hypotheticals over a bag of `n ≤ w` points is finite, with at most
`tower w q m` elements, at every level `m`; `m = ℓ` is the printed bound. -/
theorem lemma_5_81 (σ : Sig) (n w ℓ m : ℕ) (hn : n ≤ w) :
    Finite (HTh σ (Fin n) (2 * ℓ) m) ∧
      Nat.card (HTh σ (Fin n) (2 * ℓ) m) ≤ tower w (∑ i, (2 * ℓ) ^ σ.ar i) m := by sorry

end CoDecompFO
