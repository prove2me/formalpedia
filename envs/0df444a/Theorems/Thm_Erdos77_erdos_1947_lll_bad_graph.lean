-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_lll_bad_graph
-- name    : Erdos77.erdos_1947_lll_bad_graph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T10:45:07.597981+00:00
-- url     : https://prove2.me/theorems/5de41d7d-4fb9-4e2d-bc84-bbdc1d3709c9
-- title:
--   Local lemma criterion for a monochromatic-clique-free graph
-- statement:
--   For integers $2 \le k \le n$, if $4\binom{k}{2}\binom{n-2}{k-2}2^{1-\binom{k}{2}}<1$, then there is a simple graph on $n$ vertices with neither a $k$-clique nor a $k$-clique in its complement.
-- source:
--   Symmetric Lovasz local lemma applied to the monochromatic k-set events; compare J. Spencer, Ramsey's theorem-a new lower bound (1975).

import Mathlib

import Mathlib
namespace Erdos77
theorem erdos_1947_lll_bad_graph (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond : (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph (Fin n) =>
      And
        (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin n) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by sorry
end Erdos77
