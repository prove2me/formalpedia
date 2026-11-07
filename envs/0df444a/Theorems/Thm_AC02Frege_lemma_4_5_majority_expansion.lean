-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_5_majority_expansion
-- name    : AC02Frege.lemma_4_5_majority_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:25.932778+00:00
-- url     : https://prove2.me/theorems/0a77fdff-d5bc-4e90-9ab1-5a1914ec12da
-- title:
--   Lemma 4.5 — majority expansion
-- statement:
--   Let $\ell$ be odd and $h_i=\mathrm{Maj}_\ell(x_i)$. Every polynomial $p$ in the lifted variables has a unique expansion
--   $$
--   p(x)=\sum_{A\in\mathcal A}x_A\,p_A\bigl(h_1(x),\dots,h_n(x)\bigr),
--   $$
--   with every $p_A(y_1,\dots,y_n)$ multilinear. Here $\mathcal A$ is the set of $A\subseteq[n]\times[\ell]$ that select at most $m=(\ell-1)/2$ positions of every block.
--
--   The coefficient polynomials $p_A$ are what polynomial calculus for the original formula $F$ acts on; the coefficient degree and the space $\widehat C_D$ are defined through them.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - encoding: a family (p_A)_{A ∈ 𝒜} → a family indexed by all A ⊆ [n] × [ℓ] with p_A = 0 for A ∉ 𝒜 (IsExpansion); reason: the extra coordinates are forced to be zero, so the families correspond one to one
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.5, (17), p.21

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion

namespace AC02Frege

open MvPolynomial

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.5, (17), p.21 (majority expansion): for odd `ℓ`, every polynomial `p` in the
lifted variables has a unique expansion `p(x) = Σ_{A ∈ 𝒜} x_A p_A(h_1(x), …, h_n(x))` with every
`p_A(y_1, …, y_n)` multilinear.

**Formalization Note** `p` is identified with its function `ML p`; the family `q` is indexed by
all `A ⊆ [n] × [ℓ]` with `q_A = 0` off `𝒜` (`IsExpansion`), and the product is multilinearized. -/
theorem lemma_4_5_majority_expansion {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : ∃! q, IsExpansion p q := by sorry

end AC02Frege
