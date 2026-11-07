-- Prove2me | Theorems.Thm_CosDensity_lemma_8_5
-- name    : CosDensity.lemma_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:34.801752+00:00
-- url     : https://prove2.me/theorems/cac0e60c-1125-4aaa-9477-5d0d904a2ff1
-- title:
--   Lemma 8.5 with (29) — the two gadgets have equal sums $\gamma_pa_i+\beta_pe_{\chi(i)}$ and size $2^p$
-- statement:
--   Fix an integer $p>2$. For every codeword $a_i$ and coloring $\chi$,
--
--   $$\sum_{u\in\mathcal G_1(a_i)}u=\sum_{u\in\mathcal G_0(a_i)}u=\gamma_p a_i+\beta_p e_{\chi(i)},$$
--
--   where $\gamma_p=2\sum_{j\in\mathcal J_+}c_jt_j>0$ and $\beta_p=2\lambda\sum_{j\in\mathcal J_+}c_j=2^p\lambda>0$ ((29)). Moreover both gadgets contain exactly $2^p$ vectors, counting multiplicity.
--
--   This **equal-sum property** is what keeps Alice's bits from interacting: switching a gadget changes no other density.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m, every family of codewords and every coloring; reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.4, p.31 (pdf_page 32; gadget sizes) and Lemma 8.5 with (29), p.32 (pdf_page 33)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.5**, with (29) and the gadget sizes. Q. Zhang, *Frequency Moments Beyond Equality:
Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.4, p.31
(pdf_page 32, the gadget sizes) and Lemma 8.5 with (29), p.32 (pdf_page 33).

For every `i`, the one-gadget and the zero-gadget have the same vector sum, equal to
`γ_p a_i + β_p e_{χ(i)}` with `γ_p = 2 Σ_{j∈J₊} c_j t_j > 0` and `β_p = 2λ Σ_{j∈J₊} c_j = 2^p λ > 0`;
both gadgets contain exactly `2^p` vectors, counting multiplicity.

**Formalization Note.** The gadgets are lists (`gadget p a χ true i` is `G₁(a_i)`,
`gadget p a χ false i` is `G₀(a_i)`); their vector sum is `List.sum`. -/
theorem lemma_8_5 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (i : Fin N) :
    (gadget p a χ true i).sum = (gadget p a χ false i).sum ∧
    (gadget p a χ true i).sum = gammaP p • codeVec (a i) + betaP p • anchorVec (χ i) ∧
    0 < gammaP p ∧ 0 < betaP p ∧ betaP p = 2 ^ p * lam ∧
    (gadget p a χ true i).length = 2 ^ p ∧ (gadget p a χ false i).length = 2 ^ p := by sorry

end CosDensity
