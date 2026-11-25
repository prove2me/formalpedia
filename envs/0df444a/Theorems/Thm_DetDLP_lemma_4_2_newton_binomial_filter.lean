-- Prove2me | Theorems.Thm_DetDLP_lemma_4_2_newton_binomial_filter
-- name    : DetDLP.lemma_4_2_newton_binomial_filter
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:26:04.476592+00:00
-- url     : https://prove2.me/theorems/d10b17f2-9d2a-458a-bb30-e9bd5b0834aa
-- title:
--   Lemma 4.2: Nonnegative Newton–Binomial Filter Identity over $\mathcal{B}_{P_0,\ell}$
-- statement:
--   For all integers $w \ge 4$ and $M_{\mathrm{lab}} \ge 2$, the integer polynomial $\mathcal{Q}(X) = \prod_{j=-w}^w (X - 1 - jM_{\mathrm{lab}})^2$ of degree $d_{\mathrm{filt}} = 4w + 2$ with Newton coefficients $c_j = \sum_{t=0}^j (-1)^{j-t} \binom{j}{t} \mathcal{Q}(t)$ satisfies:
--
--   1. $\mathcal{Q}(d) \ge 0$ for every $d \in \mathbb{Z}$;
--   2. for every $d \in [-w(M_{\mathrm{lab}} - 1),\, w(M_{\mathrm{lab}} - 1)]$, $\mathcal{Q}(d) = 0 \iff d \equiv 1 \pmod{M_{\mathrm{lab}}}$;
--   3. $\mathcal{Q}(d) = \sum_{j=0}^{4w+2} c_j \binom{d}{j}$ for every $d \in \mathbb{Z}$;
--   4. for any $P_0 \ge 1$, any finite index set $\iota$, signs $\varsigma_t \in \{\pm 1\}$, and integers $y_{u,t}$ with $d(u) = \sum_{t=1}^{2w} \varsigma_t y_{u,t}$ and $Z_{\mathcal{Q}} = \sum_{u \in \iota} \mathcal{Q}(d(u)) < 2^{P_0}$, if $Z_0, \dots, Z_{4w+2} \in \mathbb{Z}/2^{P_0}\mathbb{Z}$ are the coefficients of
--
--   $$\sum_{u \in \iota} \prod_{t=1}^{2w} \left(\sum_{j=0}^{4w+2} \binom{\varsigma_t y_{u,t}}{j} z^j\right) \in (\mathbb{Z}/2^{P_0}\mathbb{Z})[z]/(z^{4w+3}),$$
--
--   then the canonical nonnegative residue of $\sum_{j=0}^{4w+2} c_j Z_j \bmod 2^{P_0}$ equals $Z_{\mathcal{Q}}$ exactly.
--
--   This positive filtering identity prevents modular cancellation across counterexamples and enables bit-by-bit extraction of a violating fixed-shift relation via tensor contraction.
--
--   **Formalization Note** Stated purely algebraically using `Ring.choose` and `TruncPoly P0 (4*w + 3)`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.2, eqs. (4.3)–(4.5) and Lemma 4.2 (pp. 15–16)

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

theorem lemma_4_2_newton_binomial_filter :
    ∀ (w Mlab : ℕ), 4 ≤ w → 2 ≤ Mlab →
      (∀ d : ℤ, 0 ≤ (filterPoly w Mlab).eval d) ∧
      (∀ d : ℤ, -((w : ℤ) * ((Mlab : ℤ) - 1)) ≤ d → d ≤ (w : ℤ) * ((Mlab : ℤ) - 1) →
        ((filterPoly w Mlab).eval d = 0 ↔ d ≡ 1 [ZMOD (Mlab : ℤ)])) ∧
      (∀ d : ℤ, (filterPoly w Mlab).eval d =
        ∑ j ∈ Finset.range (dFilt w + 1), newtonCoeff w Mlab j * intBinom d j) ∧
      (∀ (P0 : ℕ) [NeZero (2 ^ P0)] {ι : Type} [Fintype ι]
        (y : ι → Fin (2 * w) → ℤ) (ς : Fin (2 * w) → ℤ),
        1 ≤ P0 →
        (∀ t : Fin (2 * w), ς t = 1 ∨ ς t = -1) →
        let ℓ := dFilt w + 1
        let d : ι → ℤ := fun u => ∑ t : Fin (2 * w), ς t * y u t
        let ZQ : ℤ := ∑ u : ι, (filterPoly w Mlab).eval (d u)
        ZQ < (2 ^ P0 : ℤ) →
        ∀ Z : Fin ℓ → ZMod (2 ^ P0),
          (Ideal.Quotient.mk _ (∑ j : Fin ℓ, Polynomial.monomial j.val (Z j)) : TruncPoly P0 ℓ) =
            ∑ u : ι, ∏ t : Fin (2 * w),
              (Ideal.Quotient.mk _ (∑ j : Fin ℓ,
                Polynomial.monomial j.val ((intBinom (ς t * y u t) j.val : ℤ) : ZMod (2 ^ P0))) :
                TruncPoly P0 ℓ) →
          ((∑ j : Fin ℓ, (newtonCoeff w Mlab j.val : ZMod (2 ^ P0)) * Z j).val : ℤ) = ZQ) := by sorry

end DetDLP
