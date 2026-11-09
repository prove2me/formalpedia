-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_proposition_24
-- name    : ChvatalOneHard398.SAT.proposition_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:55.939035+00:00
-- url     : https://prove2.me/theorems/a885c476-9189-42ff-945e-efedb704db83
-- title:
--   Proposition 24 — rank one for thin residue systems
-- statement:
--   Let $m,m'\ge1$, $D\ge2$, $h\ge1$, and let $p_1,\ldots,p_s\ge2$ be pairwise coprime with $\Pi=\prod_jp_j\ge2^h$ and $p_{\max}=\max_jp_j$. Let $H\in\{0,\ldots,D-1\}^{m'\times m}$, $t\in\mathbb Z^m$, $M=\Lambda_D^\perp(H)$, and $d=Ht\bmod D$.
--   For the actual residue formulation $X=X(p,h,H,D,t)$,
--
--   $$\lambda_1(M)>\frac{m^{3/2}p_{\max}(2^h-1)}2\quad\Longrightarrow\quad R'=R_I\text{ for every rational polyhedron }R\subseteq X.$$
--
--   The conclusion includes both $R=X$ and the empty subpolyhedron. It is the rank statement for the source's constructed formulation.
--
--   Differences from the source:
--   - encoding: real coordinate vectors, integer points, and lattice notation → Fin-indexed real coordinates, explicit integer-point predicates, and Euclidean integer column spans; reason: these represent the same vectors and full-rank lattices; norms on lattices are Euclidean
--   - encoding: the standing hypotheses and X(p,h,H,D,t) of §5.3 → Params.Valid and the concrete gate-and-fixing construction; reason: all standing dimension, modulus, coprimality, box, and matrix assumptions are carried explicitly, without assuming a rank guarantee
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.24, Proposition 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Residue

namespace ChvatalOneHard398.SAT

theorem proposition_24 (a : Params) (ha : a.Valid) (hthin : IsThin a) :
    hereditaryRankOne (residuePoly a) := by sorry

end ChvatalOneHard398.SAT
