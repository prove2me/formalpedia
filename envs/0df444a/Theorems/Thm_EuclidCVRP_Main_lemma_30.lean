-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_30
-- name    : EuclidCVRP.Main.lemma_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:45.220686+00:00
-- url     : https://prove2.me/theorems/cf8f0c39-9c0e-4beb-a0c7-d49f3914185f
-- title:
--   Lemma 30 — a close smooth flow exists (corrected: the smooth flow need not satisfy f′ₑ ≤ 2n)
-- statement:
--   There are absolute constants $C>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every $n$, every square $S$ (side $s>0$, $m'\ge1$ segments per side, $m=4m'$ portals numbered clockwise from an arbitrary portal), every valid pairing flow $f$ with support $E$ and every compact ordering of $E$, there is a flow $f'$ with the same support $E$, smooth with respect to that ordering, with the same total value
--
--   $$F=\sum_{e\in E}f_e=\sum_{e\in E}f'_e,$$
--
--   that is close to $f$: some detour flow $dt$ on the portal copies transforms the in- and out-flows of $f$ into those of $f'$ at cost $c(dt)\le C\,\varepsilon\,F\,\tau(S)$.
--
--   This is what lets the dynamic program restrict to smooth flows at a small cost.
--
--   The printed lemma also asks $f'$ to be "considered by the DP", hence valid ($f'_e\le 2n$). That version is false: take the edges $(0,1)$ and $(0,2)$, at distance $1$, with $f=2n$ on both. A valid $f'$ with the same total must equal $2n$ on both, but $2n$ need not have the form $\lfloor(1+\varepsilon)^j\rfloor$. Consecutive such integers differ by more than $3$ once $(1+\varepsilon)^j>4/\varepsilon$, so for large $n$ some even values are skipped. The entry bound is therefore dropped for $f'$; it is kept for $f$.
--
--   Differences from the source:
--   - correction: a smooth flow f′ considered by the DP (valid: f′_e ≤ 2n) → a smooth flow f′ with support E (the pairing graph of f), without the entry bound 2n; reason: counterexample: E = {(0,1),(0,2)}, f = 2n on both, with 2n not of the form ⌊(1+ε)^j⌋ (such n exist for every ε > 0); same support, same total and f′ ≤ 2n force f′ = f, which violates Definition 24 (iii)
--   - generalization: smooth w.r.t. the ordering of Lemma 23 → smooth w.r.t. any given compact ordering of E; reason: the DP's ordering is a compact ordering, so this specializes to it
--   - generalization: a square of the dissection (m′ = O((1/ε) log n) even) → any square with m′ ≥ 1 segments per side and any starting portal; reason: the statement does not involve the dissection; it specializes to its squares
--   - reading: O(ε) · F · τ(S); ε sufficiently small → C ε F τ(S) with an absolute C, for ε < ε₀; reason: standing convention, p. 6
--   - reading: a detour flow dt defined over the copies of P(S) → a nonnegative integer flow on the complete directed graph on the in- and out-copies of the portals; reason: all flows of §4 are integer flows; the paper states no further condition on dt
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 29, Lemma 30 (with Definition 29, pp. 28–29)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Pairing

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Lemma 30** (p. 29), corrected. Given any valid pairing flow `f` for a square `S` with support `E`,
and any compact ordering of `E`, there is a flow `f'` on the same support `E` (a pairing graph), smooth
with respect to that ordering, with the same total flow value `F`, that is close to `f`
(Definition 29). The `O(ε)` of closeness is an absolute constant `C`.

Correction: the printed statement asks for a smooth flow "considered by the DP", i.e. also valid
(`f'_e ≤ 2n`). That is false: for the edges `(0,1)`, `(0,2)` (distance 1) with `f = 2n` on both, a valid
`f'` with the same total must equal `2n` on both, and `2n` need not be of the form `⌊(1+ε)^j⌋`
(consecutive such integers differ by more than 3 once `(1+ε)^j > 4/ε`, so even integers are skipped). The entry bound `2n` is
therefore not required of `f'`. -/
theorem lemma_30 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ (n : ℕ) (S : DSquare), 0 < S.side → 0 < S.m' →
        ∀ (E : Finset PEdge) (f : PEdge → ℕ), IsValidFlow S.m n E f →
        ∀ l : List PEdge, IsCompactOrdering S.m E l →
          ∃ f' : PEdge → ℕ, IsPairingGraph S.m E ∧ IsSmooth ε l f' ∧ S.IsClose C ε E f f' := by sorry

end EuclidCVRP.Main
