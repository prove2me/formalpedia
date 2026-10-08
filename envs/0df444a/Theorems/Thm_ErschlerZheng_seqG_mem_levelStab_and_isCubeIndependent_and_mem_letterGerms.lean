-- Prove2me | Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
-- name    : ErschlerZheng.seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T03:36:01.588081+00:00
-- url     : https://prove2.me/theorems/5b199e40-8236-4415-a603-fb94a9204d39
-- title:
--   (7.1), p. 35 — g_n fixes level n with sections aγ or γa; (g_n) is cube independent on 1^∞·G_ω; g_n has b-germs if ω_{n−1} ≠ 2 and c-germs if ω_{n−1} = 2
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), and let $g_n$ be the elements (7.1) of $G_\omega$ (`seqG`). Write $\gamma = c$ if $\omega_{n-1} = \mathbf 2$ and $\gamma = b$ otherwise. Then:
--
--   1. for every $n \ge 1$, $g_n$ lies in the level-$n$ stabilizer of $G_\omega$ (`levelStab`), and its section (`sec`) at every vertex $v$ of length $n$ is $a\gamma_{\mathfrak s^n\omega}$ or $\gamma_{\mathfrak s^n\omega}a$ (written $a \cdot (a\gamma_{\mathfrak s^n\omega}) \cdot a$; `evalWord ω n`);
--   2. the sequence $(g_n)$ has the cube independence property on the orbit $1^\infty \cdot G_\omega$ (`IsCubeIndependent`, `orbitOne`), with all parameters $k_n = 1$;
--   3. for every $n \ge 1$: if $\omega_{n-1} \ne \mathbf 2$, then at every point $x$ of the orbit the germ $(g_n, x)$ lies in $\mathcal H^b$, the germs that are trivial or $b$ (`letterGerms ω .b`); if $\omega_{n-1} = \mathbf 2$, then every germ $(g_n, x)$ lies in $\mathcal H^c$ (`letterGerms ω .c`) and some germ $(g_n, x)$ is not in $\mathcal H^b$.
--
--   Erschler and Zheng, p. 35: “First take the sequence of words obtained by substitutions: (7.1) $g_n = \zeta_{\omega_0} \circ \ldots \zeta_{\omega_{n-1}}(ab_{\mathfrak s^n\omega})$ if $\omega_{n-1} \neq \mathbf 2$, $\zeta_{\omega_0} \circ \ldots \zeta_{\omega_{n-1}}(ac_{\mathfrak s^n\omega})$ if $\omega_{n-1} = \mathbf 2$. The sequence $(g_n)$ has the cube independence property by Lemma 5.6. From its definition in (7.1), $g_n$ has $b$-germs if $\omega_{n-1} \neq \mathbf 2$ and $c$-germs if $\omega_{n-1} = \mathbf 2$.”
--
--   The first part is what “by Lemma 5.6” asserts of $g_n$: Lemma 5.6 (p. 27) asks that $g_n \in \mathrm{St}_G(\mathsf L_n)$ and that “the root permutation of the section $(g_n)_v$ has no fixed point for all $v \in \mathsf L_n$”, and $a\gamma$ and $\gamma a$ are the sections the substitutions produce. The second part is the sentence's cube independence, with the constant parameters of p. 26 (“When the parameters $k_n$ are constant 1, we omit reference to $\mathbf k$”). In the third part, “$g_n$ has $b$-germs” is read as: every germ of $g_n$ at a point of the orbit is trivial or a $b$-germ, that is, lies in $\mathcal H^b$ of p. 42 (“Let $H = \langle b \rangle < (\mathcal G_\omega)_o$ and $\mathcal H^b$ be the set of germs that are either trivial or $b$ as in (3.1).”); “$c$-germs” likewise, with $\mathcal H^c$ (`letterGerms ω .c`), together with one germ outside $\mathcal H^b$. The standing assumption is that of §7.2 (p. 35: “Throughout the rest of this section we assume that $\omega$ satisfies Assumption $(\mathrm{Fr}(D))$”).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 35, the sequence (7.1)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) :
    (∀ n, 1 ≤ n → seqG ω n ∈ levelStab (grigorchuk ω) n ∧
      ∀ v : List Bool, v.length = n →
        sec (seqG ω n) v = evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b] ∨
          sec (seqG ω n) v =
            Garrido.grigA * evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b] * Garrido.grigA) ∧
    IsCubeIndependent (orbitOne ω) (fun _ => 1) (seqG ω) ∧
    ∀ n, 1 ≤ n →
      (ω (n - 1) ≠ 2 → ∀ x ∈ orbitOne ω, (seqG ω n, x) ∈ letterGerms ω .b) ∧
      (ω (n - 1) = 2 → (∀ x ∈ orbitOne ω, (seqG ω n, x) ∈ letterGerms ω .c) ∧
        ∃ x ∈ orbitOne ω, (seqG ω n, x) ∉ letterGerms ω .b) := by
  sorry

end ErschlerZheng
