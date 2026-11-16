-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_theorem_10
-- name    : DirKECC1549.Main.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:22:49.470212+00:00
-- url     : https://prove2.me/theorems/fc0fa902-74c7-4e5a-9221-472d264972f9
-- title:
--   Theorem 10 — lower bound: ⌊n/(k+2)⌋·3^ℓ k-vertex-connected components of size ℓ+1
-- statement:
--   For every integer $k\ge7$ let $\ell=\lfloor (k-1)/3\rfloor$. For every integer $n\ge k+2$ there is a simple undirected graph $G$ with $n$ vertices containing at least
--   $$\Big\lfloor\frac{n}{k+2}\Big\rfloor\,3^{\ell}$$
--   distinct $k$-vertex-connected components, each of size $\ell+1$. Consequently the number of $k$-vertex-connected components can be $\Omega\big(\tfrac nk3^{k/3}\big)$ and their total size can be $\Omega(n3^{k/3})$: there is an absolute constant $c>0$ such that the same graph $G$ also satisfies
--   $$|C_k(G)|\ \ge\ c\,\frac nk\,3^{k/3}\qquad\text{and}\qquad\|C_k(G)\|\ \ge\ c\,n\,3^{k/3}.$$
--
--   This shows that the exponential term $3^{k/3}$ of Theorem 9 is best possible.
--
--   **Formalization Note** $c$ is chosen before $k$ and $n$; one graph $G$ satisfies all three conclusions; $3^{k/3}$ is the real power.
--
--   Differences from the source:
--   - encoding: Ω(·) bounds stated as consequences → one absolute constant c > 0, before k and n, with both bounds for the same graph G; reason: the paper derives both from the constructed G with explicit constants (t ≥ n/(2(k + 2)), 3^ℓ ≥ 3^{k/3}/3)
--   - encoding: simple undirected graph with n vertices → SimpleGraph (Fin n); reason: Lean convention; same instances
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Theorem 10, p.35 (proof pp.35–36)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_Undirected

set_option autoImplicit false

open Finset

namespace DirKECC1549.Main.Supplement

/-- Theorem 10, p.35: for every integer `k ≥ 7`, with `ℓ = ⌊(k − 1)/3⌋`, and every integer
`n ≥ k + 2`, there is a simple undirected graph `G` on `n` vertices with at least
`⌊n/(k + 2)⌋·3^ℓ` distinct `k`-vertex-connected components of size `ℓ + 1`; consequently the
number of `k`-vertex-connected components can be `Ω((n/k)·3^{k/3})` and their total size
`Ω(n·3^{k/3})`. The constant `c` of both `Ω` bounds is absolute (chosen before `k` and `n`), and one
graph `G` satisfies all three conclusions. -/
theorem theorem_10 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), 7 ≤ k → ∀ (n : ℕ), k + 2 ≤ n →
        ∃ G : SimpleGraph (Fin n),
          n / (k + 2) * 3 ^ ell k ≤ ((kvccFamily k G).filter (fun K => K.card = ell k + 1)).card ∧
          c * ((n : ℝ) / (k : ℝ)) * (3 : ℝ) ^ ((k : ℝ) / 3) ≤ ((kvccFamily k G).card : ℝ) ∧
          c * (n : ℝ) * (3 : ℝ) ^ ((k : ℝ) / 3) ≤ (kvccTotalSize k G : ℝ) := by sorry

end DirKECC1549.Main.Supplement
