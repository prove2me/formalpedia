-- Prove2me | Theorems.Thm_ErschlerZheng_hasVolumeExponent_firstString_alpha0
-- name    : ErschlerZheng.hasVolumeExponent_firstString_alpha0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:12:33.007584+00:00
-- url     : https://prove2.me/theorems/fca54587-b3fe-4fe1-b90a-8d05a680de84
-- title:
--   p. 3 and the abstract — the volume exponent of the first Grigorchuk group exists and equals α_0: log log v_{G,S}(n)/log n → α_0
-- statement:
--   For the first Grigorchuk group $G = G_{012}$, the group $G_\omega$ for $\omega = (\mathbf{012})^\infty$ (`firstString`), with the generating set $S = \{a, b, c, d\}$ (`genSet firstString`),
--   $$\lim_{n \to \infty} \frac{\log\log v_{G,S}(n)}{\log n} = \alpha_0,$$
--   where $v_{G,S}$ is the growth function and $\alpha_0 = \log 2/\log\lambda_0$ (`alpha0`), $\lambda_0$ the positive root of $X^3 - X^2 - 2X - 4$ (`HasVolumeExponent`).
--
--   Erschler and Zheng, p. 3: “The volume lower bound in Theorem A matches up in exponent with Bartholdi’s upper bound in [5]. In particular, combined with the upper bound we conclude that the volume exponent of the first Grigorchuk group $G$ exists and is equal to $\alpha_0$, that is $\lim_{n \to \infty} \frac{\log\log v_{G,S}(n)}{\log n} = \alpha_0$. It was open whether the limit exists.”
--
--   The abstract (p. 1) states the same limit: “In particular, for the first Grigorchuk group $G$ we show that its growth $v_{G,S}(n)$ satisfies $\lim_{n \to \infty} \log\log v_{G,S}(n)/\log n = \alpha_0$, where $\alpha_0 = \frac{\log 2}{\log \lambda_0} \approx 0.7674$, $\lambda_0$ is the positive root of the polynomial $X^3 - X^2 - 2X - 4$.”
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 3, the volume exponent of G_012, and the abstract

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem hasVolumeExponent_firstString_alpha0 :
    HasVolumeExponent (genSet firstString) alpha0 := by
  sorry

end ErschlerZheng
