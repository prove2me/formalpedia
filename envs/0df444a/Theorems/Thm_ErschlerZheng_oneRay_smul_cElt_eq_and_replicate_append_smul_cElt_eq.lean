-- Prove2me | Theorems.Thm_ErschlerZheng_oneRay_smul_cElt_eq_and_replicate_append_smul_cElt_eq
-- name    : ErschlerZheng.oneRay_smul_cElt_eq_and_replicate_append_smul_cElt_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T04:46:25.877607+00:00
-- url     : https://prove2.me/theorems/cf5bf6fa-e029-415a-bdc7-bdf3237a55ef
-- title:
--   Remark 7.8 — 𝔠^v_j fixes the ray 1^∞ and every vertex 1^m0
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $D$ divide $k$ and let $v \in \mathsf V^j_k$ (`vSet`). Then $\mathfrak c^v_j$ (`cElt`) fixes the ray $1^\infty$ (`oneRay`), and for every $m \ge 0$ it fixes the vertex $1^m0$.
--
--   Erschler and Zheng, p. 39, Remark 7.8: “The reason we need $\mathbf{201}$ or $\mathbf{211}$ in Assumption $(\mathrm{Fr}(D))$ to perform these conjugations is the following: the digit $\mathbf 2$ is needed for $[b, a]$ to be in the rigid stabilizer at the corresponding level, the second digit different from $\mathbf 2$ implies $[b, a]$ acts as $ab, ba$ on the next level, and the last digit $\mathbf 1$ implies that the sections of $c$ that gets swapped are $c$ and $id$. As a consequence, $\mathfrak c^v_j$ fixes the ray $1^\infty$ and vertices of the form $1^m0$.”
--
--   The statement is the consequence in the last sentence of the remark. The facts the explanation draws on, for the windows $\mathbf{201}$ and $\mathbf{211}$, are stated in [`ErschlerZheng.length_and_hElt_mem_rist_and_oneRay_smul_hProd`](https://prove2.me/theorems/d9949906-c0e1-49c1-b297-a6bb20d4b23e) (the rigid stabilizer, and $[b, a]$ acting as $ba$ below $1$) and in Lemma 7.7, [`ErschlerZheng.smul_cElt_eq_self_and_sec_cElt_eq`](https://prove2.me/theorems/e7667dd5-2b8d-4953-a310-071b76bcec22) (the sections of $\mathfrak c^v_j$); the remark's “needed” is the authors' motivation and is not formalized. The assumption $(\mathrm{Fr}(D))$ is the standing assumption of §7.2 (p. 35).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 39, Remark 7.8

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem oneRay_smul_cElt_eq_and_replicate_append_smul_cElt_eq (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) :
    oneRay <• cElt ω j v = oneRay ∧
      ∀ m : ℕ, (List.replicate m true ++ [false]) <• cElt ω j v =
        List.replicate m true ++ [false] := by
  sorry

end ErschlerZheng
