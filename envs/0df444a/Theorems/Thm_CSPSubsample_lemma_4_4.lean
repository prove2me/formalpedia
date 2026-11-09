-- Prove2me | Theorems.Thm_CSPSubsample_lemma_4_4
-- name    : CSPSubsample.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:23:34.657293+00:00
-- url     : https://prove2.me/theorems/1efb0b4c-dbff-41a8-979f-691f1d69b536
-- title:
--   Lemma 4.4 — the bias $|\mathbb E f(Z)-f(x)|\le k^2/N$
-- statement:
--   Fix $x\in X$ and $N\in[n]$, and let $Z\sim\mathcal D(x,N)$. Then
--   $$
--   \big|\mathbb E[f(Z)]-f(x)\big|\le\frac{k^2}{N}.
--   $$
--   Together with Lemma 4.2 it bounds $|f(Z)-f(x)|$, which is $|\mathrm{val}_U(\phi)-\mathrm{val}(\phi)|$ when the sample has no repeated variable.
--
--   Differences from the source:
--   - encoding: x ∈ X and Z ∼ D(x, N), the empirical mean of N i.i.d. pairs (i_t, a_t) with P[(i_t, a_t) = (i, a)] = x_{i,a} → x = x(ϕ) for an assignment ϕ, and Z the empirical mean of the pairs (s_t, ϕ(s_t)) for a uniform index sequence s ∈ [n]^N; probabilities and E are finite averages over the n^N sequences; reason: under x(ϕ) the pair (i, a) has probability 𝕀{ϕ_i = a}/n, so a draw is (i_t, ϕ(i_t)) with i_t uniform; the law of Z is the same
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 4.4, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_probWR
import Definitions.Def_CSPSubsample_fPoly

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 4.4** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.10 = PDF p.12). Fix `x ∈ X`,
`N ∈ [n]`, and let `Z ∼ D(x, N)`. Then `|E[f(Z)] − f(x)| ≤ k²/N`.

**Formalization Note** As in Lemma 4.2: `x = x(ϕ)`, `Z = Zemp ϕ s` with `s` uniform on
`Fin N → Fin n`, `E` is the finite average `expWR`; `N ∈ [n]` is `1 ≤ N ≤ n`. -/
theorem lemma_4_4 {n k q : ℕ} (I : Instance n k q) (ϕ : Fin n → Fin q) (N : ℕ) (hN1 : 1 ≤ N)
    (hNn : N ≤ n) :
    |expWR n N (fun s => fPoly I (Zemp ϕ s)) - fPoly I (xAlg ϕ)| ≤ (k : ℝ) ^ 2 / N := by sorry

end CSPSubsample
