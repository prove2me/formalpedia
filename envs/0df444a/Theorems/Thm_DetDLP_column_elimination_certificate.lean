-- Prove2me | Theorems.Thm_DetDLP_column_elimination_certificate
-- name    : DetDLP.column_elimination_certificate
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:39:45.613063+00:00
-- url     : https://prove2.me/theorems/ae2ac38c-6f56-450f-a909-c36e03d84b62
-- title:
--   Correctness of bounded column Hermite elimination
-- statement:
--   Let $m>0$ and let $C$ be an arbitrary list of integer columns in dimension $n$. The specified algorithm for bounded Hermite elimination returns exactly $n$ columns, whose matrix $D$ is in lower triangular column Hermite form. For every subgroup $H$ of $\mathbb Z^n$,
--   $$\{D_j\}_j\subseteq H\quad\Longleftrightarrow\quad C\subseteq H\ \text{ and }\ m\mathbb Z^n\subseteq H.$$
--   This characterizes the actual output lattice, including inputs with redundant or dependent columns.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Algorithmic refinement of Lemma 4.4, Section 4.3.

import Definitions.Def_DetDLP_BorderedHermite

set_option autoImplicit false

namespace DetDLP
open BorderedHermite

theorem column_elimination_certificate {n : ℕ} {m : ℤ} (hm : 0 < m) (cols : Array (Column n)) :
    let out := normalForm m cols
    out.size = n ∧ IsColumnHNF (asMatrix out) ∧
      ∀ H : AddSubgroup (Fin n → ℤ), (∀ c ∈ out, c.get ∈ H) ↔
        (∀ c ∈ cols, c.get ∈ H) ∧ (∀ i : Fin n, (Pi.single i m : Fin n → ℤ) ∈ H) := by sorry
end DetDLP
