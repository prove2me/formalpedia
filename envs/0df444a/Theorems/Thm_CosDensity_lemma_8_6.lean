-- Prove2me | Theorems.Thm_CosDensity_lemma_8_6
-- name    : CosDensity.lemma_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:43.348773+00:00
-- url     : https://prove2.me/theorems/f0166956-5efb-449f-891a-a5c939e16c79
-- title:
--   Lemma 8.6 — moment isolation: $\sum_{\mathcal G_1}\langle u,s\rangle^p-\sum_{\mathcal G_0}\langle u,s\rangle^p=\kappa_pZ_i^p$
-- statement:
--   Fix an integer $p>2$. Let $s$ be a vector with no component in any balancing direction: $\langle g_c,s\rangle=0$ for every color $c$. Put $B_i=\lambda\langle e_{\chi(i)},s\rangle$ and $Z_i=\langle a_i,s\rangle$. Then $\langle u_{i,j,\sigma},s\rangle=B_i+t_jZ_i$ for every $i$, every level $0\le j\le p$ and every sign $\sigma$, and
--
--   $$\sum_{u\in\mathcal G_1(a_i)}\langle u,s\rangle^p-\sum_{u\in\mathcal G_0(a_i)}\langle u,s\rangle^p=\kappa_pZ_i^p,\qquad \kappa_p=2\,p!\,h^p.\qquad(30)$$
--
--   The local baseline $B_i$ cancels, so a one-gadget adds exactly $\kappa_pZ_i^p$ to the moment.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m, every family of codewords and every coloring; reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.4, Lemma 8.6, p.32 (pdf_page 33)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.6** (moment isolation). Q. Zhang, *Frequency Moments Beyond Equality: Streaming
Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.4, Lemma 8.6,
p.32 (pdf_page 33).

Let `s` have no component in any balancing direction `g_c`. With `B_i = λ ⟨e_{χ(i)}, s⟩` and
`Z_i = ⟨a_i, s⟩`, every level-`j` gadget vector has `⟨u_{i,j,σ}, s⟩ = B_i + t_j Z_i`, and
`Σ_{u∈G₁(a_i)} ⟨u, s⟩^p − Σ_{u∈G₀(a_i)} ⟨u, s⟩^p = κ_p Z_i^p` with `κ_p = 2 p! h^p` (30).

**Formalization Note.** "No component in any balancing direction" is `⟨g_c, s⟩ = 0` for every
color `c ∈ [m]`. The sums over the multisets `G_b(a_i)` are sums over the lists `gadget`. -/
theorem lemma_8_6 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (s : Amb m) (hs : ∀ c : Fin m, ⟪balVec c, s⟫ = 0) :
    (∀ (i : Fin N) (j : ℕ) (σ : Bool), j ≤ p →
      ⟪gadgetVec p a χ i j σ, s⟫ = anchorBase χ i s + level p j * codeResp a i s) ∧
    ∀ i : Fin N,
      ((gadget p a χ true i).map (fun u => ⟪u, s⟫ ^ p)).sum -
          ((gadget p a χ false i).map (fun u => ⟪u, s⟫ ^ p)).sum =
        kappa p * codeResp a i s ^ p := by sorry

end CosDensity
