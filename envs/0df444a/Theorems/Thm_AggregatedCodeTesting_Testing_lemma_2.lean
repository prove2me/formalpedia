-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_lemma_2
-- name    : AggregatedCodeTesting.Testing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:11.18914+00:00
-- url     : https://prove2.me/theorems/057240d2-e368-436a-bde3-a5bcade1045b
-- title:
--   Lemma 2 — integer Krawtchouk moments, generating function, orthogonality and likelihood expansion
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code, $w\ge1$ and $\ell\in(\mathbb F_2^m)^w$, with moments $c_\ell(r)=\mathbb E_\ell\,\psi_r(H)$, $\psi_r(h)=\prod_eK_{r_e}(h_e)$, and $G_\ell(z)=\prod_{j}g_{\ell_j}(z)$, $g_\sigma(z)=\sum_{A\in C^\perp}\chi_A(\sigma)z^A$. Let $B$ be the product of $m$ independent $\mathrm{Bin}(w,1/2)$ laws. Then:
--
--   1. every moment $c_\ell(r)$ is an integer;
--   2. $G_\ell(z)=\sum_r c_\ell(r)z^r$, i.e. the coefficient of $z^r$ in $G_\ell$ is $c_\ell(r)$ for every multi-index $r$;
--   3. for $r,r'\in\{0,\dots,w\}^m$,
--   $$
--   \mathbb E_B[\psi_r\psi_{r'}]=[r=r']\binom{w}{r};
--   $$
--   4. for every $h\in\{0,\dots,w\}^m$,
--   $$
--   \frac{\Pr_\ell[H=h]}{B(h)}=\sum_{r\in\{0,\dots,w\}^m}\frac{c_\ell(r)}{\binom{w}{r}}\psi_r(h);
--   $$
--   5. for every $\ell'$ of the same width, $P_\ell=P_{\ell'}$ if and only if $c_\ell(r)=c_{\ell'}(r)$ for all $r$.
--
--   The lemma converts the observation law into integer coordinates in an orthogonal basis; integrality is what later allows exact recovery by rounding.
--
--   Differences from the source:
--   - generalization: stated in §3.1 on an informative indecomposable block → stated for every binary linear code $C\le\mathbb F_2^m$; reason: the identities do not use indecomposability or informativeness, and an informative indecomposable block is such a code.
--   - encoding: multi-indices $r\in\{0,\dots,w\}^m$ in items 1, 2 and 5 → all $r\in\mathbb N^m$; reason: for $r_e>w$ both $c_\ell(r)$ (since $K_j=0$ for $j>w$) and the coefficient of $z^r$ in $G_\ell$ (degree at most $w$ in each variable) vanish, so the statements are equivalent.
--   - encoding: $G_\ell=\prod_\sigma g_\sigma^{n_\sigma(\ell)}$ → $\prod_j g_{\ell_j}$; reason: $g$ depends only on the coset, so the products are equal.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Lemma 2, printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Orders

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-- Lemma 2 (integer moments and orthogonality), printed p. 4 (PDF p. 5): the moments
`c_ℓ(r)` are integers; `G_ℓ(z) = ∑_r c_ℓ(r) z^r`; `E_B[ψ_r ψ_{r′}] = [r = r′] binom(w, r)` for
`r, r′ ∈ {0,…,w}^m`; `Pr_ℓ[H = h] / B(h) = ∑_r c_ℓ(r)/binom(w, r) ψ_r(h)`; and two laws agree
exactly when all their moments agree. -/
theorem lemma_2 {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (w : ℕ) (hw : 0 < w)
    (ℓ : Fin w → Word m) :
    (∀ r : Fin m → ℕ, ∃ k : ℤ, moment C ℓ r = (k : ℝ)) ∧
    (∀ r : Fin m →₀ ℕ, ((MvPolynomial.coeff r (genPoly C ℓ) : ℤ) : ℝ) = moment C ℓ r) ∧
    (∀ r r' : Fin m → ℕ, r ∈ lowIndices m w → r' ∈ lowIndices m w →
      ∑ h, binomProd w h * (psi w r h : ℝ) * (psi w r' h : ℝ) =
        if r = r' then (multiBinom w r : ℝ) else 0) ∧
    (∀ h : Fin m → Fin (w + 1), law C ℓ h / binomProd w h =
      ∑ r ∈ lowIndices m w, moment C ℓ r / (multiBinom w r : ℝ) * (psi w r h : ℝ)) ∧
    (∀ ℓ' : Fin w → Word m, law C ℓ = law C ℓ' ↔ ∀ r : Fin m → ℕ, moment C ℓ r = moment C ℓ' r) := by sorry

end AggregatedCodeTesting.Testing
