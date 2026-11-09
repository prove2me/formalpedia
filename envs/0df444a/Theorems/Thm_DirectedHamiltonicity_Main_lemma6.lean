-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_lemma6
-- name    : DirectedHamiltonicity.Main.lemma6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:24.709465+00:00
-- url     : https://prove2.me/theorems/bf2a7118-c4ea-47f7-b12a-363d439425ef
-- title:
--   Lemma 6 — the polynomial cancellation space has dimension at most $p-1$
-- statement:
--   Let $K$ be a field and let $p,d\ge1$ be integers. Let $z_{i\ell}$, for $i\in[p]$ and $\ell\in[d]$, be distinct indeterminates of a polynomial ring $R$ over $K$ (which may have further indeterminates), and let $f_1,\dots,f_p\in R$ be nonzero polynomials. Then the vector space
--   $$W=\Bigl\{c\in K^{[p]\times[d]}:\ \sum_{i=1}^p\sum_{\ell=1}^d c_{i\ell}\,z_{i\ell}\,f_i=0\Bigr\}$$
--   satisfies $\dim_K W\le p-1$. In particular, if $K=\mathbb F_2$, then $|W|\le2^{p-1}$.
--
--   No linear independence of the $f_i$, no degree bound and no restriction on the characteristic is assumed. The lemma bounds how often a random linear combination of the shifted polynomials $z_{i\ell}f_i$ can cancel, which drives the induction of Lemma 5.
--
--   Differences from the source:
--   - encoding: a polynomial ring R over K containing indeterminates z_{iℓ} → MvPolynomial σ K with an injective map z : Fin p × Fin d → σ; reason: a polynomial ring over K in an arbitrary set σ of indeterminates; injectivity says the z_{iℓ} are distinct
--   - encoding: if K = F₂ → if Nat.card K = 2; reason: every field with two elements is isomorphic to F₂, and |W| is invariant under the isomorphism
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.6 / printed p.5, Lemma 6 (proof PDF p.7 / printed p.6)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies

namespace DirectedHamiltonicity.Main

open Multidigraph

/-- Lemma 6, PDF p.6 / printed p.5: for nonzero polynomials `f_1, …, f_p` in a polynomial ring over
a field `K` with distinct indeterminates `z_{iℓ}` (`i ∈ [p]`, `ℓ ∈ [d]`, `p, d ≥ 1`), the space `W` of
coefficient vectors `c` with `∑_i ∑_ℓ c_{iℓ} z_{iℓ} f_i = 0` has dimension at most `p − 1`; if `K` is
the two-element field, `|W| ≤ 2^{p−1}`. -/
theorem lemma6 (K σ : Type) [Field K] (p d : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (z : Fin p × Fin d → σ) (hz : Function.Injective z) (f : Fin p → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) :
    Module.finrank K (cancelSpace z f) ≤ p - 1 ∧
      (Nat.card K = 2 → Nat.card (cancelSpace z f) ≤ 2 ^ (p - 1)) := by sorry

end DirectedHamiltonicity.Main
