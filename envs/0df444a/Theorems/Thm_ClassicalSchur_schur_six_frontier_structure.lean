-- Prove2me | Theorems.Thm_ClassicalSchur_schur_six_frontier_structure
-- name    : ClassicalSchur.schur_six_frontier_structure
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:42.002686+00:00
-- url     : https://prove2.me/theorems/919960bd-101d-47c3-a81e-50f3d3ca9a2a
-- title:
--   Structure of a six-colour Schur colouring of $[1, 1801]$ under $R_4(3) \le 61$: balance, saturation and reflection
-- statement:
--   This is the goal of the mission: the structure that a Schur colouring of $[1, 1801]$ with six colours must have if $R_4(3) \le 61$.
--
--   Suppose that $\mathrm{TR}(4, 61)$ holds (Lean `TriangleRamsey 4 61`): every colouring with at most four colours of the pairs of a finite set of at least $61$ naturals has a monochromatic triangle, that is, $R_4(3) \le 61$. Let $c : \mathbb{N} \to \mathrm{Fin}\,6$ be a Schur colouring of $[1, 1801]$ with six colours: there are no $x, y \ge 1$ with $x + y \le 1801$ and $c(x) = c(y) = c(x + y)$. Write $q = c(901)$, let
--
--   $$
--   V = \{\, x \in [0, 1801] : x \ne 900,\ c(|900 - x|) = q \,\}
--   $$
--
--   be the central neighbourhood, for $v \in \mathbb{N}$ and a colour $i$ let $\Gamma_i(V, v) = \{\, w \in V : w \ne v,\ c(|v - w|) = i \,\}$, and let $P_i = \Gamma_i(V, 1801)$ be the endpoint neighbourhood of colour $i$. Then:
--
--   1. every colour $j$ occurs $150$ times in $[1, 900]$: $\bigl|\{\, d \in [1, 900] : c(d) = j \,\}\bigr| = 150$;
--   2. $|V| = 301$;
--   3. for every $v \in V$ and every colour $i \ne q$: $|\Gamma_i(V, v)| = 60$;
--   4. for every $d$ with $1 \le d \le 900$ and $c(d) = q$: $c(901 - d) = c(901 + d)$;
--   5. for every colour $i \ne q$: $|P_i| = 60$; for every $x \in P_i$, $1800 - x \in P_i$ and $1800 - x \ne x$; and for all $x, y \in P_i$ with $x \ne y$, $c(|x - y|) \ne i$ and $c(|x - y|) \ne q$.
--
--   The central part of the statement is
--
--   $$
--   |V| = 301, \qquad |\Gamma_i(V, v)| = 60 \ \ (v \in V,\ i \ne q), \qquad c(901 - d) = c(901 + d) \ \ (d \in [1, 900],\ c(d) = q).
--   $$
--
--   Under $R_4(3) \le 61$ the pigeonhole step gives $R_5(3) \le 302$ and the centred bound then gives $S(6) \le 1801$, so $[1, 1801]$ is the frontier interval for six colours. The theorem shows that a Schur colouring of $[1, 1801]$ with six colours yields five sets $P_i$ of $60$ points, each the union of $30$ pairs $\{900 - d, 900 + d\}$, whose differences use only the four colours other than $i$ and $q$; so to exclude such a colouring it is sufficient to exclude these sets. It is a structure theorem for a hypothetical colouring: it does not prove $S(6) \le 1800$, and it does not decide whether such a colouring exists.
--
--   **Formalization Note.** $R_4(3) \le 61$ is a hypothesis, not a proved fact of the mission; if $R_4(3) > 61$, or if no Schur colouring of $[1, 1801]$ with six colours exists, the statement holds vacuously, and whether such a colouring exists is open. $\mathrm{TR}(4, 61)$ quantifies over colourings, with colours in any `Finset` of at most four naturals, of the pairs $x < y$ of any finite set of at least $61$ naturals. The colouring $c$ is a function on all of $\mathbb{N}$, constrained only on $[1, 1801]$, and $x = y$ is allowed in a Schur triple. $V$ lies in `range 1802` $= [0, 1801]$, so the point $0$ is a candidate member. The subtractions $901 - d$ (with $d \le 900$) and $1800 - x$ (with $x \in P_i$, so $x \le 1800$) are truncated subtractions on $\mathbb{N}$ that never truncate here, and distances are `Nat.dist`.
-- source:
--   Note "The frontier of the centred Schur bound: balance, saturation and reflection" (schur-numbers project, 2026-10-02, unpublished), section "Six colours under R_4(3) ≤ 61". Lean proof not yet in a public repository.

import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.schur_six_frontier_structure (hR : TriangleRamsey 4 61) {c : ℕ → Fin 6}
    (hc : SchurColoring 1801 c) :
    (∀ j, ((Icc 1 900).filter fun d => c d = j).card = 150) ∧
    (centralNbhd c 900).card = 301 ∧
    (∀ v ∈ centralNbhd c 900, ∀ i ≠ c 901, (colorNbhd c (centralNbhd c 900) v i).card = 60) ∧
    (∀ d, 0 < d → d ≤ 900 → c d = c 901 → c (901 - d) = c (901 + d)) ∧
    ∀ i ≠ c 901, (endpointNbhd c 900 i).card = 60 ∧
      (∀ x ∈ endpointNbhd c 900 i, 1800 - x ∈ endpointNbhd c 900 i ∧ 1800 - x ≠ x) ∧
      ∀ x ∈ endpointNbhd c 900 i, ∀ y ∈ endpointNbhd c 900 i, x ≠ y →
        c (Nat.dist x y) ≠ i ∧ c (Nat.dist x y) ≠ c 901 := by sorry
