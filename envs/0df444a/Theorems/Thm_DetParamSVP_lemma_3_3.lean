-- Prove2me | Theorems.Thm_DetParamSVP_lemma_3_3
-- name    : DetParamSVP.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:30.107608+00:00
-- url     : https://prove2.me/theorems/ba8bc7bf-ef9e-49d9-9e07-474777a7cac3
-- title:
--   Lemma 3.3 — the Reed–Solomon lattice has $\lambda_1^{(p)}(\mathcal L_{q,k})\ge(2k)^{1/p}$
-- statement:
--   Let $k\ge2$ and let $q>2k$ be prime. The lattice
--
--   $$\mathcal L_{q,k}=\Big\{v\in\mathbb Z^{\mathbb F_q}:\sum_{z\in\mathbb F_q}v_z z^j\equiv0\pmod q\ \ (0\le j<k)\Big\}\tag{5}$$
--
--   satisfies $\lambda_1^{(p)}(\mathcal L_{q,k})\ge(2k)^{1/p}$ for every $p\ge1$; the equation for $j=0$ uses $z^0=1$ for every $z$.
--
--   The bound is cited from Bennett and Peikert [BP23, Theorem 3.1]; it gives the minimum-distance condition of the locally dense lattice built in Theorem 3.4.
--
--   Differences from the source:
--   - encoding: λ₁^{(p)}(L_{q,k}) ≥ (2k)^{1/p} → every nonzero v ∈ L_{q,k} has ‖v‖_p ≥ (2k)^{1/p}; reason: the minimum over a discrete set is attained
--   - encoding: q prime → the instance Fact q.Prime; reason: Lean convention; it also makes the coordinate set ZMod q finite
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 3.3 and Eq. (5), p.19 (citing [BP23, Theorem 3.1])

import Definitions.Def_DetParamSVP_LpNorm
import Definitions.Def_DetParamSVP_RSConstruction

set_option autoImplicit false

namespace DetParamSVP

/-- **Lemma 3.3** ([BP23, Theorem 3.1]). Let `k ≥ 2` and let `q > 2k` be prime. The Reed–Solomon
lattice `L_{q,k}` of Eq. (5) satisfies `λ₁^{(p)}(L_{q,k}) ≥ (2k)^{1/p}` for every `p ≥ 1`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 3.3, p.19.

**Formalization Note.** `λ₁ ≥ (2k)^{1/p}` is written "every nonzero `v ∈ L_{q,k}` has
`‖v‖_p ≥ (2k)^{1/p}`". Primality of `q` is the instance `Fact q.Prime`, which also makes the
coordinate set `ZMod q` finite. -/
theorem lemma_3_3 (q k : ℕ) [Fact q.Prime] (hk : 2 ≤ k) (hqk : 2 * k < q) (p : ℝ) (hp : 1 ≤ p) :
    ∀ v ∈ rsLattice q k, v ≠ 0 → ((2 * k : ℕ) : ℝ) ^ (1 / p) ≤ lpNorm p v := by sorry

end DetParamSVP
