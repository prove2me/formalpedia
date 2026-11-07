-- Prove2me | Theorems.Thm_CosDensity_lemma_8_8
-- name    : CosDensity.lemma_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:57.174018+00:00
-- url     : https://prove2.me/theorems/3cd624d7-bd60-4e9d-b09b-5864aabf487d
-- title:
--   Lemma 8.8 — $0\le V_0(q)\le C_VQ^p$
-- statement:
--   Fix an integer $p>2$, $\iota\in(0,1/2)$, $C_R>0$ and $c_N>0$. There are $C_V>0$ and $m_0$ such that for every $m\ge m_0$, with $N=m\lfloor c_Nm^{\rho_p-1}\rfloor$, every family of unit codewords with nonnegative coordinates satisfying (35) and (36), every balanced coloring and every query $q$,
--
--   $$0\le V_0(q)\le C_V\,Q^p,$$
--
--   where $V_0(q)=M_p(P(0,q))$ is the moment of the all-zero instance.
--
--   The global baseline is of the same order as the queried signal $\kappa_pQ^p$, which gives a constant multiplicative gap.
--
--   Differences from the source:
--   - reading: C_V = C_V(p, ν), for the parameters ι and c_N chosen from ν in Lemma 8.7 and the constant C_R of (35) → C_V and m₀ chosen after arbitrary ι ∈ (0, 1/2), C_R > 0, c_N > 0; reason: the paper's instance is the case ι = ι(ν), c_N = c_N(ν); the proof bounds V₀ for any fixed parameters
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.6, Lemma 8.8, pp.34–35 (pdf_page 35–36), with (35)–(36), p.33 (pdf_page 34)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.8** (the global baseline). Q. Zhang, *Frequency Moments Beyond Equality: Streaming
Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.6, Lemma 8.8,
pp.34–35 (pdf_page 35–36), with (35)–(36), p.33 (pdf_page 34).

There is a constant `C_V` such that, for all sufficiently large `m` and every query `q`,
`0 ≤ V₀(q) ≤ C_V Q^p`, where `V₀(q) = M_p(P(0, q))`.

**Formalization Note.** The paper's `C_V = C_V(p, ν)` is a constant for the code parameter `ι` and
the constant `c_N` chosen from `ν` in Lemma 8.7, and for the constant `C_R` of (35). Here `C_V` and
the threshold `m₀` are chosen after every `ι ∈ (0, 1/2)`, `C_R > 0` and `c_N > 0`, which contains
that instance. For `m ≥ m₀`, `N = m ⌊c_N m^{ρ_p−1}⌋`, every unit nonnegative code satisfying (35)
and (36), every balanced coloring and every `q`, the bound holds. -/
theorem lemma_8_8 (p : ℕ) (hp : 2 < p) (ι : ℝ) (hι0 : 0 < ι) (hι1 : ι < 1 / 2) (CR : ℝ)
    (hCR : 0 < CR) (cN : ℝ) (hcN : 0 < cN) :
    ∃ CV : ℝ, 0 < CV ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (a : Fin (codeLength p cN m) → EuclideanSpace ℝ (Fin m))
        (χ : Fin (codeLength p cN m) → Fin m),
        IsUnitNonnegCode a → IsBalanced χ →
        (∀ i, rowSum a i ≤ CR * rMax p (codeLength p cN m) m) →
        (∀ q, ∑ i ∈ Finset.univ.erase q, ⟪a i, a q⟫ ^ p ≤ ι) →
        ∀ q : Fin (codeLength p cN m),
          0 ≤ baseline p a χ q ∧ baseline p a χ q ≤ CV * queryAmp p m ^ p := by sorry

end CosDensity
