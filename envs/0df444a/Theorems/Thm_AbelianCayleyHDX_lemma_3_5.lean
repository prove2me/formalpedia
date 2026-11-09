-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_3_5
-- name    : AbelianCayleyHDX.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:38:55.952322+00:00
-- url     : https://prove2.me/theorems/3e54cfd6-1ddb-4fd9-9c90-db01eba621d0
-- title:
--   Lemma 3.5 — row and column weights of $H_D$; $P_D$ is a normalized adjacency operator
-- statement:
--   Let $q = 2^h \ge 8$, $F = \mathbb F_{q^2}$, $t \ge 1$, $V_0 = F^t$, and let $D \subseteq \mathrm{PG}(t-1, F)$ be spanning (the standing assumptions of Section 3); let $\hat\nu = |\hat D|$ and $M = |\Omega|$. Then $H_D \in \mathbb F_2^{R \times M}$ with
--   $$R = \frac{(q^2 - 2)\hat\nu M}{6};$$
--   its rows are distinct and have weight three; every column has weight $\rho = (q^2 - 2)\hat\nu/2$; and no pair of columns occurs together in more than one row. Consequently $\tilde H_D^{\mathsf T}\tilde H_D - \rho I$ is the adjacency matrix of a simple $2\rho$-regular graph — the graph on $\Omega$ joining two columns that share a row — and $P_D := P_{H_D}$ of (2.1) is its normalized adjacency operator.
--
--   Differences from the source:
--   - encoding: $F = \mathbb F_{q^2}$ → any finite field with $q^2$ elements; reason: all such fields are isomorphic to $\mathbb F_{q^2}$
--   - encoding: $q = 2^h \ge 8$ → $h \in \mathbb N$ with $8 \le 2^h$; reason: same parameters
--   - encoding: $R = (q^2-2)\hat\nu M/6$ and $\rho = (q^2-2)\hat\nu/2$ → $6R = (q^2-2)\hat\nu M$ and $2\rho = (q^2-2)\hat\nu$ in $\mathbb N$; reason: avoids natural-number division; $q^2 - 2$ is exact since $q^2 \ge 64$
--   - encoding: the adjacency matrix of a simple $2\rho$-regular graph → the adjacency matrix of the column graph (columns sharing a row), which is $2\rho$-regular; reason: a 0/1 symmetric matrix with zero diagonal determines its graph; Lemma 3.7 refers to this graph
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.5, p.12

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_rowWeight
import Definitions.Def_AbelianCayleyHDX_colWeight
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_colGraph
import Definitions.Def_AbelianCayleyHDX_PD

namespace AbelianCayleyHDX

open Classical in
/-- **Lemma 3.5** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.5, p.12). Let `q = 2^h ≥ 8`, `F = 𝔽_{q²}`, `t ≥ 1`,
`V₀ = F^t` and `D ⊆ PG(t − 1, F)` spanning (the standing assumptions of Section 3), and let
`ν̂ = |D̂|` and `M = |Ω|`. The matrix `H_D` has `R = (q² − 2) ν̂ M / 6` rows; its rows are
distinct and have weight three; every column has weight `ρ = (q² − 2) ν̂ / 2`; and no pair of
columns occurs together in more than one row. Consequently `H̃_Dᵀ H̃_D − ρ I` is the adjacency
matrix of a simple `2ρ`-regular graph (the graph on `Ω` joining two columns that share a row), and
`P_D := P_{H_D}` of (2.1) is its normalized adjacency operator.

**Formalization Note** `F` is any finite field with `q²` elements. Rows are indexed by the triples
`(b, x, ℓ)`; `R = (q² − 2) ν̂ M / 6` is written `6R = (q² − 2) ν̂ M` and `ρ` through `2ρ = (q² − 2) ν̂`.
The natural-number subtraction `q² − 2` is exact (`q² ≥ 64`). -/
theorem lemma_3_5 (h : ℕ) (hq : 8 ≤ 2 ^ h) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) {t : ℕ} (ht : 1 ≤ t) (D : Finset (PG t F))
    (hD : IsSpanning D) :
    6 * Fintype.card (RowIdx D) = ((2 ^ h) ^ 2 - 2) * (Dhat D).card * Fintype.card (Omega F t) ∧
    Function.Injective (HD D) ∧
    (∀ r, rowWeight (HD D) r = 3) ∧
    (∀ c, 2 * colWeight (HD D) c = ((2 ^ h) ^ 2 - 2) * (Dhat D).card) ∧
    (∀ c c' : Omega F t, c ≠ c' →
      (Finset.univ.filter fun r => HD D r c = 1 ∧ HD D r c' = 1).card ≤ 1) ∧
    (∀ ρ : ℕ, 2 * ρ = ((2 ^ h) ^ 2 - 2) * (Dhat D).card →
      (colGraph D).IsRegularOfDegree (2 * ρ) ∧
      (Htilde (HD D)).transpose * Htilde (HD D) - (ρ : ℝ) • (1 : Matrix (Omega F t) (Omega F t) ℝ) =
        (colGraph D).adjMatrix ℝ ∧
      PD D = (1 / (2 * (ρ : ℝ))) • (colGraph D).adjMatrix ℝ) := by sorry

end AbelianCayleyHDX
