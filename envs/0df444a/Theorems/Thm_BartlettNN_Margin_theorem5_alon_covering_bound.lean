-- Prove2me | Theorems.Thm_BartlettNN_Margin_theorem5_alon_covering_bound
-- name    : BartlettNN.Margin.theorem5_alon_covering_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:05:53.09907+00:00
-- url     : https://prove2.me/theorems/c4683d63-27d9-4647-a9f9-eb127c6b8f6e
-- title:
--   Theorem 5 [Alon et al.] — log₂ N∞(F, 2, n) < 1 + log₂(nb²) log₂(Σ_{i≤d} C(n,i) bⁱ)
-- statement:
--   Let $F$ be a class of functions from $\{1,\dots,n\}$ to $\{1,\dots,b\}$ with $\operatorname{fat}_F(1)\le d$. If
--   $$
--   n\ \ge\ 1+\log_2\Bigl(\sum_{i=0}^{d}\binom ni b^i\Bigr),
--   $$
--   then
--   $$
--   \log_2\mathcal N_\infty(F,2,n)\ <\ 1+\log_2(nb^2)\,\log_2\Bigl(\sum_{i=0}^{d}\binom ni b^i\Bigr).
--   $$
--   Here $\mathcal N_\infty(F,2,n)$ is the largest, over samples of length $n$ from $\{1,\dots,n\}$, of the size of the smallest $2$-cover of $F$ in the sample $\ell_\infty$ pseudometric.
--
--   This is the scale-sensitive analogue of the Sauer–Shelah lemma due to Alon, Ben-David, Cesa-Bianchi and Haussler; the paper cites it without proof and applies it to a quantized class.
--
--   **Formalization Note** The domain $\{1,\dots,n\}$ is `Fin n` (indexed from $0$); the values $1,\dots,b$ are natural numbers viewed as reals. The conclusion asserts that $\mathcal N_\infty(F,2,n)$ is finite and states the logarithmic bound for its value. $\mathcal N_\infty$ is the maximum over all samples $x\in\{1,\dots,n\}^n$, repetitions allowed, as in the paper's definition.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 528, Theorem 5 (cited from Alon, Ben-David, Cesa-Bianchi, Haussler, J. ACM 44 (1997))

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Theorem 5** (Bartlett 1998, p. 528, cited from Alon, Ben-David, Cesa-Bianchi and
Haussler [1]). Let `F` be a class of functions from `{1, …, n}` (here `Fin n`) to `{1, …, b}` with
`fat_F(1) ≤ d`. If `n ≥ 1 + log₂(∑_{i=0}^{d} C(n, i) b^i)`, then `N∞(F, 2, n)` is finite and
`log₂ N∞(F, 2, n) < 1 + log₂(n b²) log₂(∑_{i=0}^{d} C(n, i) b^i)`. -/
theorem theorem5_alon_covering_bound (n b d : ℕ) (F : Set (Fin n → ℝ))
    (hF : ∀ f ∈ F, ∀ i, ∃ k : ℕ, 1 ≤ k ∧ k ≤ b ∧ f i = k)
    (hfat : fat F 1 ≤ d)
    (hn : 1 + Real.logb 2 (∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ) * (b : ℝ) ^ i) ≤ n) :
    Ninf F 2 n < ⊤ ∧
      Real.logb 2 ((Ninf F 2 n).toNat : ℝ) <
        1 + Real.logb 2 ((n : ℝ) * (b : ℝ) ^ 2) *
          Real.logb 2 (∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ) * (b : ℝ) ^ i) := by sorry

end BartlettNN.Margin
