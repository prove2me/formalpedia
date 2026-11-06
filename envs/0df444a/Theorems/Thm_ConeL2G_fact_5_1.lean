-- Prove2me | Theorems.Thm_ConeL2G_fact_5_1
-- name    : ConeL2G.fact_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:18.331002+00:00
-- url     : https://prove2.me/theorems/49ca4636-8bc9-4452-8f06-f14fafbd3298
-- title:
--   Fact 5.1 — $\Pi_{i,c}h$ as a difference of averages when $c$ is unused
-- statement:
--   Let $H$ be a finite graph with color lists, $\mu_H$ uniform on its proper list colorings, $c$ a color and $x$ a proper list coloring of $H$ in which no vertex has color $c$. Then for every $h\in L^2(\mu_H)$ and every vertex $i$
--   $$\mathop{\mathbb E}_{a\sim L_i^{-c-x_{N_H(i)}}}\big[h(x^{i\to a})\big]-\mathop{\mathbb E}_{a\sim L_i^{-x_{N_H(i)}}}\big[h(x^{i\to a})\big]=(\Pi^H_{i,c}h)(x),$$
--   where $a\sim S$ is uniform on $S$, $x^{i\to a}$ agrees with $x$ except that its $i$-th coordinate is $a$, and $L_i^{-c-x_{N_H(i)}}=L_i^{-x_{N_H(i)}}\setminus\{c\}$.
--
--   The identity expresses the effect of forbidding the color $c$ at $i$ through the rank-one projection, which is how the center of a cone enters the leaf computations.
--
--   Differences from the source:
--   - encoding: x ∈ Ω^{−c}_H → x ∈ properColorings H L and x j ≠ c for every j; reason: Ω^{−c}_H (p.16) is the set of proper list colorings using no color c; same set
--   - encoding: E_{a∼S}[φ(a)], x^{i→a} → (1/|S|) Σ_{a∈S} φ(a), Function.update x i a; reason: a ∼ S is uniform on S (p.7); same values
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Fact 5.1, p.16

import Mathlib
import Definitions.Def_ConeL2G_properColorings
import Definitions.Def_ConeL2G_avail
import Definitions.Def_ConeL2G_projPi

open Finset

namespace ConeL2G

/-- **Fact 5.1 (`Π_{i,c}` as a difference of averages when `c` is unused).** Li–Oveis Gharan,
arXiv:2610.37721, Fact 5.1, p.16: "For every `h ∈ L²(µ_H)`, every color `c`, every `x ∈ Ω_H^{−c}`, and
every `i ∈ H`, we have
`E_{a∼L_i^{−c−x_{N_H(i)}}}[h(x^{i→a})] − E_{a∼L_i^{−x_{N_H(i)}}}[h(x^{i→a})] = (Π^H_{i,c}h)(x)`."

`Ω_H^{−c}` (p.16) is the set of proper list colorings of `H` that use no vertex color `c`;
`a ∼ S` is uniform on `S` (p.7), so `E_{a∼S}[φ(a)] = (1/|S|) Σ_{a∈S} φ(a)`; `x^{i→a}` is
`Function.update x i a`; `L_i^{−c−x_{N_H(i)}} = (avail H L i x).erase c`.

**Formalization Note.** `H` and its lists are arbitrary (the lists left after pinning). -/
theorem fact_5_1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {K : ℕ} (L : V → Finset (Fin K)) (h : (V → Fin K) → ℝ) (c : Fin K) (x : V → Fin K)
    (hx : x ∈ properColorings H L) (hxc : ∀ j : V, x j ≠ c) (i : V) :
    (1 / (((avail H L i x).erase c).card : ℝ)) *
          ∑ a ∈ (avail H L i x).erase c, h (Function.update x i a) -
        (1 / ((avail H L i x).card : ℝ)) * ∑ a ∈ avail H L i x, h (Function.update x i a) =
      projPi H L i c h x := by sorry

end ConeL2G
