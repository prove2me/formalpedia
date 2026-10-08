-- Prove2me | Theorems.Thm_AffinePolicies_TwoGap_lemma_2
-- name    : AffinePolicies.TwoGap.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:56.470931+00:00
-- url     : https://prove2.me/theorems/1bf1d92e-9ab3-4f0e-95f5-8818bfbc8775
-- title:
--   Lemma 2, PDF p. 11 — 𝒰 of (6) is permutation-invariant with respect to every τ ∈ Γ
-- statement:
--   Let $m$ be even and let $\mathcal U = \operatorname{conv}\{0, e_1,\dots,e_m, b^{m+1}, b^{m+2}\}$ be the uncertainty set of the instance (6). Let $\Gamma$ be the set (10) of permutations $\tau$ of $\{1,\dots,m\}$ with $i \le m/2 \iff \tau(i) \le m/2$. Then for every $\tau \in \Gamma$ and every $x \in \mathbb R^m$,
--   $$x\in\mathcal U \iff x^{\tau}=(x_{\tau(1)},\dots,x_{\tau(m)})\in\mathcal U .$$
--
--   This symmetry is what allows an optimal affine policy to be averaged over $\Gamma$ in Lemma 3.
--
--   **Formalization Note** $x^\tau$ is `x ∘ τ`. Indices are 0-based, so $\Gamma$ is the set of `τ` with `(i : ℕ) < m / 2 ↔ (τ i : ℕ) < m / 2` for all `i`.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 2 (with Definition 2 and (10)), PDF p. 11

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem lemma_2 (m : ℕ) (hm_even : Even m) :
    ∀ τ ∈ Gamma m, IsPermInvariant (U6 m) τ := by sorry

end AffinePolicies.TwoGap
